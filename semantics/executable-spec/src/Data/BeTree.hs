{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Implements a prototype B-epsilon tree. It is virtual in that nodes
--   are not stored on disk, but in main memory. It exhibits the correct
--   behavior, buffering messages, flushing them down the tree when the message
--   buffer becomes full, and splitting nodes when the subtree space becomes full.
module Data.BeTree where

import Data.List (sortBy)
import qualified Data.Map.Strict as Map
import Data.Ratio ((%))
import Data.FingerTree hiding (fromList)
import qualified Data.FingerTree as FT
import Debug.Trace

-- ===================================================================

data Function v = Identity | Plus v | Compose (Function v) (Function v)
  deriving Show

class Exp t where
  plus:: t -> t -> t

applyExp :: Exp v => Function v -> v -> v
applyExp Identity x = x
applyExp (Plus n) x = plus n x
applyExp (Compose f g) x = applyExp f (applyExp g x)

data Message v
  = Edit v -- Change the value to v, if it is there, otherwise insert v if it is not
  | Delete
  | Upsert (Function v)

-- Composition, apply the operator on the right first
merge :: Exp v => Message v -> Message v -> Message v
merge Delete _ = Delete
merge (Edit x) Delete = Edit x
merge (Edit x) (Edit _) = Edit x
merge (Edit x) (Upsert _) = Edit x

merge (Upsert Identity) (Edit x) = Edit x
merge (Upsert Identity) Delete = Delete
merge (Upsert Identity) (Upsert exp) = Upsert exp

merge (Upsert (Plus v)) (Edit x) = Edit (plus v x)
merge (Upsert (Plus v)) Delete = Delete
merge (Upsert (Plus v)) (Upsert exp) = Upsert (Compose (Plus v) exp)
merge (Upsert (Compose f g)) x = merge (Upsert f) (merge (Upsert g) x)

newtype Delta k v = Delta (Map.Map k (Message v))
  deriving Show

applyMessages :: (Ord k,Exp v) => Map.Map k v -> Delta k v -> Map.Map k v
applyMessages m (Delta messages) = Map.foldlWithKey' acc m messages
  where
    acc ans key Delete = Map.delete key ans
    acc ans key (Edit v) = Map.insert key v ans
    acc ans key (Upsert Identity) = ans
    acc ans key (Upsert (Plus n)) = Map.update (\ x -> Just(plus n x)) key ans

-- ========================================

-- A Split has either One or Two parts. If it has 2 parts, pair each part with its smallest key.
data Split k x = One x | Two (k, x) (k, x)
  deriving (Show)

-- | Spit a map at 'k', 'k' should be the smallest key in the right result.
splitMapWithKey :: Ord k => k -> Map.Map k a -> (Map.Map k a, Map.Map k a)
splitMapWithKey k m =
  case Map.splitLookup k m of
    (left, Nothing, right) -> (left, right)
    (left, Just v, right) -> (left, Map.insert k v right)

-- | Split a map into roughly 2 equal size pieces. Pair each piece with its smallest key.
splitMap :: Map.Map c b -> (c, Map.Map c b, c, Map.Map c b)
splitMap m = (k1, m1, k2, m2)
  where
    (m1, m2) = Map.splitAt (Map.size m `div` 2) m
    (k1, _) = Map.findMin m1
    (k2, _) = Map.findMin m2

-- ======================================================
-- An Internal node has 2 maps. The first represents the Internal nodes subtree descendants.
-- And the second represents messages that will be "flushed" to one or more of those subtrees.
-- Suppose the subtrees look like [(3,d1),(9,d2),(12,d3),(20,d4)] where d1,d2,d3,d4 are
-- the descendant subtrees, 3,9,12,20 are keys that determine the key-range stored in the
-- associated decendants. The question arises which messages go to each of these descendants.
-- keys such that (      key <  9) go to d1
--                (9  <= key < 12) go to d2
--                (12 <= key < 20) go to d3
--                (20 <= key)      go to d4
-- We call each of these ranges an Interval. There are three kinds of Intervals. The ranges above
-- are represented as: [(First 3 9),(Middle 9 12),(Middle 12 20),(Last 20)]
-- Think of these as intervals (closed at the bottom, open at the top), Note that the First (and Last)
-- entries have no lower (upper) bounds. In (First lo hi) 'lo' is not a lower bound, just the smallest
-- element inserted so far in d1. Things smaller than 'lo' can be legally be inserted. For (Last lo hi),
-- 'hi' is not an upperbound, only the largest key inserted into d4 so far.

data Interval k
  = First k k -- First  lo hi  [Negative Infinity .. hi)
  | Middle k k -- Middle lo hi  [lo .. hi)
  | Last k -- Last lo       [lo .. Infinity)
  deriving (Show)

-- | If an Interval describes a map, what is its least key. Special reasoning for a First Interval
newkey :: Ord a => Interval a -> Map.Map a b -> a
newkey (First lo _) m =
  if Map.null m
    then lo
    else min lo (fst (Map.findMin m))
newkey (Middle lo _) _ = lo
newkey (Last lo) _ = lo

-- =============================================================
-- BeTree nodes have two parts, whose size is related by epsilon
{- =============================================================

|------subtrees------------|---messagebuffer---|
|------------------Internal--------------------|
|---------------------Leaf---------------------|

============================================== -}

nodesize :: Int
nodesize = 10

-- | In a Internal node, the fraction reserved for subtrees
epsilon :: Rational
epsilon = 1 % 2

subtreesize :: Int
subtreesize = floor $ (fromIntegral nodesize) * epsilon

buffersize :: Int
buffersize = nodesize - subtreesize

data BeTree k v
  = Leaf (Map.Map k v)
  | Internal (Map.Map k (BeTree k v)) (Delta k v)

-- ========================================================
-- Operations on BeTrees

emptyBeTree :: BeTree k v
emptyBeTree = Leaf (Map.empty)

isempty :: BeTree k v -> Bool
isempty (Leaf dats) = Map.null dats
isempty (Internal m1 (Delta m2)) = Map.null m1 && Map.null m2

insertB :: (Exp v,Ord k) => k -> v -> BeTree k v -> BeTree k v
insertB k v tree =
  case applyFlushSplit tree (Delta (Map.singleton k (Edit v))) of
    One x -> x
    Two (k1, t1) (k2, t2) -> internalOpt (Map.fromList [(k1, t1), (k2, t2)]) (Delta Map.empty)

lookupB :: (Exp v,Ord k) => k -> BeTree k v -> Maybe v
lookupB key (Leaf x) = Map.lookup key x
lookupB key (Internal subtrees (Delta buffer)) =
  case Map.lookup key buffer of
    Just (Edit x) -> Just x
    Just (Delete) -> Nothing
    Just (Upsert f) -> applyExp f <$> (findB key subtrees)
    Nothing -> (findB key subtrees)

findB :: (Exp v,Ord k) => k -> Map.Map k (BeTree k v) -> Maybe v
findB key subtrees =
  case Map.splitLookup key subtrees of
    (_, Just tree, _) -> lookupB key tree
    (less, Nothing, _) ->
      if Map.null less
        then Nothing
        else lookupB key (snd (Map.findMax less))

-- ==========================================================
-- helper functions that do the hard work.

-- | Never build an Internal Node with one or zero subtrees and no messages
internalOpt :: Map.Map k (BeTree k v) -> Delta k v -> BeTree k v
internalOpt subtrees (Delta buffer)
  | Map.null subtrees && Map.null buffer = Leaf Map.empty
  | Map.size subtrees == 1 && Map.null buffer = snd (Map.findMin subtrees)
  | True = Internal subtrees (Delta buffer)

-- | Applying some messages to a BeTree may cause 
--   1) a flush if the message buffer becomes over full
--   2) a split, if there is no room for all the applied values.
applyFlushSplit :: (Exp v,Ord k) => BeTree k v -> Delta k v -> Split k (BeTree k v)
applyFlushSplit (Leaf m1) (Delta m2)
  | newsize <= nodesize = One (Leaf new)
  | True =
    let (k1, leaf1, k2, leaf2) = splitMap new
     in Two (k1, Leaf leaf1) (k2, Leaf leaf2)
  where
    new = (applyMessages m1 (Delta m2))
    newsize = Map.size new
applyFlushSplit (Internal subtrees (Delta buffer)) (Delta m2)
  -- Messages fit in the buffer
  | newsize <= buffersize = One (internalOpt subtrees (Delta new))
  -- The trialSubtrees is small enough so we don't have to split
  | Map.size trialSubtrees <= subtreesize = One (internalOpt trialSubtrees (Delta (newbuffer)))
  -- We have to spit the Internal node into 2 Internal nodes.
  | True = Two (k1, internalOpt subtrees1(Delta buffer1)) (k2, internalOpt subtrees2 (Delta buffer2))
  where
    new = Map.unionWith merge m2 buffer
    newsize = Map.size new
    (key, subtree, flushmap) = chooseFlush subtrees new
    newbuffer = Map.difference new flushmap
    trialSubtrees =
      case applyFlushSplit subtree (Delta flushmap) of
        One x -> (Map.insert key x subtrees)
        Two (key1, t1) (key2, t2) -> Map.insert key1 t1 (Map.insert key2 t2 (Map.delete key subtrees))
    (k1, subtrees1, k2, subtrees2) = splitMap trialSubtrees
    (buffer1, buffer2) = splitMapWithKey k2 newbuffer

-- ===================================================================
-- Choosing where to flush some messages

-- | Collect the range intervals of the subtree descendant map.
--   for example if: m1 = Map.fromList [(3,"one"),(9,"two"),(12,"three"),(20,"four")]
--   ranges m1 == [(First 3 9,"one"),(Middle 9 12,"two"),(Middle 12 20,"three"),(Last 20,"four")]
ranges :: Map.Map k a -> [(Interval k, a)]
ranges m1 = fixFirst (collectTriples (Map.toAscList m1))
  where
    collectTriples :: [(k, a)] -> [(Interval k, a)]
    collectTriples [] = []
    collectTriples [(k, a)] = [(Last k, a)]
    collectTriples ((k1, a1) : (k2, a2) : more) = (Middle k1 k2, a1) : collectTriples ((k2, a2) : more)
    fixFirst [] = []
    fixFirst [pair] = [pair]
    fixFirst ((Middle l h, a) : more) = (First l h, a) : more
    fixFirst xs = xs

-- | Given an interval, compute a subset of all entries from 'ms' in that interval.
--   The interval is closed on the low side (i.e. includes low), and open
--   on the high side (does not include high). If (First lo hi) think
--   of 'lo' as negative infinity, and if (Last lo hi)  think of 'hi' as infinity.
getRange :: Ord k => Interval k -> Map.Map k m -> Map.Map k m
getRange (First _low high) ms =
  case Map.split high ms of
    (n1, _) -> n1
getRange (Last low) ms =
  case Map.splitLookup low ms of
    (_, atlow, n2) -> addM low atlow n2
getRange (Middle low high) ms =
  case Map.splitLookup low ms of
    (_m1, atlow, m2) ->
      case Map.split high m2 of
        (n1, _) -> addM low atlow n1

addM :: Ord k => k -> Maybe a -> Map.Map k a -> Map.Map k a
addM _key Nothing m = m
addM key (Just v) m = Map.insert key v m

-- | For each subtree in the 'descMap', compute the key Interval that it stores.
--   Use that Interval to compute a subset of the 'messageMap', that can be flushed
--   down into that subtree. Count the size of that subset. Choose
--   1) the key of the subtree
--   2) The subtree
--   3) The subset of the 'messageMap' applicable to that subtree
--   with the largest count.
chooseFlush ::
  Ord k =>
  Map.Map k b ->
  Map.Map k a ->
  (k, b, Map.Map k a)
chooseFlush descMap messageMap = best
  where
    descRanges = ranges descMap
    splits =
      map
        ( \(interval, desc) ->
            let changes = getRange interval messageMap
             in (Map.size changes, (newkey interval changes, desc, changes))
        )
        descRanges
    comp x y = compare (fst y) (fst x) -- we want largest first
    best = case sortBy comp splits of
      [] -> error ("No largest in empty list")
      ((_, triple) : _) -> triple

-- ================================================================
-- Converting between [(k,v)], (Map.Map k v), and (BeTree k v)

fromList :: (Exp v,Ord k) => [(k, v)] -> BeTree k v -> BeTree k v
fromList [] ans = ans
fromList ((k, v) : more) ans = fromList more (insertB k v ans)

beTreeToMap :: (Exp v, Ord k) => BeTree k v -> Map.Map k v
beTreeToMap (Leaf x) = x
beTreeToMap (Internal subtrees messages) =
  applyMessages
    (Map.unions (Map.elems (Map.map beTreeToMap subtrees)))
    messages

mapToBeTree :: (Exp v,Ord k) => Map.Map k v -> BeTree k v
mapToBeTree m = fromList (Map.assocs m) (Leaf Map.empty)

-- ==============================================
-- Instance Monoid for Message and Delta

instance Exp v => Semigroup (Message v) where
  (<>) = merge

instance Exp v => Monoid (Message v) where
  mempty = Upsert Identity
  mappend = (<>)


instance Show v => Show(Message v) where
  show (Edit n) = "(Edit "++show n++")"
  show Delete = "Delete"
  show (Upsert x) = "(Upsert "++show x++")"

instance (Ord k,Exp v) => Semigroup (Delta k v) where
 (<>) (Delta x) (Delta y) = Delta (Map.unionWith merge x y)

instance (Ord k,Exp v) => Monoid (Delta k v) where
  mempty = Delta (Map.empty)

-- ==========================================
-- Finger Trees and sequences with partial sums

-- | A Partial is Monoid made from a Pair of Monoids,
--  the first part of the Pair (the sum for) Int,
--  the second part is Accumulated Delta appications 
data Partial k v = Partial Int (Delta k v)
  deriving Show


instance (Ord k,Exp v) => Semigroup (Partial k v) where
  (<>) (Partial n x) (Partial m y) = Partial (n + m) (x <> y)

instance (Ord k,Exp v) => Monoid (Partial k v) where
  mempty = Partial 0 mempty



instance (Ord k,Exp v) => Measured (Partial k v) (Delta k v) where
  measure m = (Partial 1 m)



one (k,t) = Delta (Map.singleton k t)

actions :: [Delta Char Int]
actions = [one('a',Upsert (Plus 2)),one('b',Edit 3), one('b',Delete),one('a',Edit 2)]



timeline :: FingerTree (Partial Char Int) (Delta Char Int)
timeline = FT.fromList actions


ss :: (Ord k,Show k,Exp v,Show v) => FingerTree (Partial k v) (Delta k v) -> IO ()
ss x = case viewl x of
        EmptyL -> pure ()
        (a :< xs) ->
          case measure x of
            Partial index acc ->
              putStrLn ("element = "++show a++", cummulative action = "++show acc++", index = "++show index) >> ss xs

disp xs = putStrLn "" >> (ss xs)


-- the computed index "flows" from right to left, because the element at the end of the sequence was added first
-- For example, the sequence of Messages  [Upsert (+2),Edit 3,Delete,Edit 2], has this internal shape, where
-- the first line is the left most element of the sequence.
-- element = Upsert, cummulative action = (Edit 5), index = 4
-- element = (Edit 3), cummulative action = (Edit 3), index = 3
-- element = Delete, cummulative action = Delete, index = 2
-- element = (Edit 2), cummulative action = (Edit 2), index = 1


hasindex i (Partial n _) (Partial m _) = n>i 


-- | Update a particular index with 'message' at key 'k, the cumulative actions are recomputed in log time.
update :: (Ord k,Exp v) => Int -> k -> Message v -> FingerTree (Partial k v) (Delta k v) ->  FingerTree (Partial k v) (Delta k v)
update i k message timeline =
  case search (hasindex i) timeline of
    Position left (Delta old) right -> left >< (Delta(Map.insertWith merge k message old) <| right )


instance Exp Int where plus x y = x+y
