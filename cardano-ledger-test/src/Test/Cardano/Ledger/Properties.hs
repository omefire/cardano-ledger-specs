{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Test.Cardano.Ledger.Properties where

--import Debug.Trace (trace)

--import Cardano.Ledger.Mary.Value (Value (..))

--ScriptPurpose (..),

--hashWitnessPPData,

--Positive (..),

import Cardano.Ledger.Alonzo (AlonzoEra, Value)
import Cardano.Ledger.Alonzo.Data (Data, DataHash, hashData)
import Cardano.Ledger.Alonzo.Language (Language (..))
import Cardano.Ledger.Alonzo.PParams (PParams, PParams' (..))
import Cardano.Ledger.Alonzo.Rules.Utxow (AlonzoUTXOW)
import Cardano.Ledger.Alonzo.Scripts
import Cardano.Ledger.Alonzo.Tx
  ( IsValid (..),
    ValidatedTx (..),
    minfee,
  )
import Cardano.Ledger.Alonzo.TxBody (TxBody (..), TxOut (..))
import Cardano.Ledger.Alonzo.TxWitness (RdmrPtr (..), Redeemers (..), TxDats (..), TxWitness (..))
import Cardano.Ledger.BaseTypes (Network (Testnet), StrictMaybe (..))
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Hashes (EraIndependentTxBody, ScriptHash (..))
import Cardano.Ledger.Keys
  ( GenDelegs (..),
    KeyHash (..),
    KeyPair (..),
    KeyRole (..),
    coerceKeyRole,
    hashKey,
  )
import Cardano.Ledger.SafeHash (SafeHash, hashAnnotated)
import Cardano.Ledger.ShelleyMA.Timelocks (Timelock (..), ValidityInterval (..))
import Cardano.Ledger.Val
import Cardano.Slotting.Slot (SlotNo (..))
import Control.Monad (foldM, forM, replicateM, zipWithM)
import Control.Monad.Trans.Class
import Control.Monad.Trans.RWS.Strict
import Control.State.Transition.Extended hiding (Assertion)
import Data.ByteString.Short (ShortByteString)
import Data.Default.Class (Default (def))
import qualified Data.Foldable as F
import Data.List (sort)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Maybe.Strict (strictMaybe)
import Data.Ratio ((%))
import qualified Data.Sequence.Strict as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Numeric.Natural
import Plutus.V1.Ledger.Api (defaultCostModelParams)
import Shelley.Spec.Ledger.API
  ( Addr (..),
    CLI (evaluateTransactionFee),
    Credential (..),
    StakeReference (..),
    TxIn (..),
    UTxO (..),
    Wdrl (..),
  )
import Shelley.Spec.Ledger.LedgerState (UTxOState (..))
import Shelley.Spec.Ledger.STS.Utxo (UtxoEnv (..))
import Shelley.Spec.Ledger.Tx (hashScript)
import Shelley.Spec.Ledger.UTxO (balance, makeWitnessVKey)
import Test.Cardano.Ledger.Alonzo.Serialisation.Generators ()
import Test.QuickCheck
import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (C_Crypto)
import Test.Shelley.Spec.Ledger.Serialisation.EraIndepGenerators ()
import Test.Shelley.Spec.Ledger.Utils
  ( RawSeed,
    applySTSTest,
    mkKeyPair',
    runShelleyBase,
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (Arbitrary (..), Gen, forAll, testProperty)

type A = AlonzoEra C_Crypto

-- newtype KeySpace = KeySpace [(KeyHash 'Witness C_Crypto, KeyPair 'Witness C_Crypto)]
--   deriving (Show)

-- genListBetween :: Int -> Int -> Gen a -> Gen [a]
-- genListBetween a b g = chooseInt (a, b) >>= flip vectorOf g

-- data Vault a b = Vault
--   { sid :: [a],
--     sec :: Map a b
--   }

-- data BagOSecrets = BagOSecrets
--   { keys :: Vault (KeyHash 'Witness C_Crypto) (KeyPair 'Witness C_Crypto),
--     timelocks :: Vault (ScriptHash C_Crypto) (Timelock A, [KeyPair 'Witness C_Crypto]),
--     plutons :: Vault (ScriptHash C_Crypto) ShortByteString,
--     datums :: Vault (DataHash C_Crypto) (Data A)
--   }

-- newtype NotTooSmallInputSet = NotTooSmallInputSet (Set (TxIn C_Crypto))
--   deriving (Show)

-- instance Arbitrary NotTooSmallInputSet where
--   arbitrary = NotTooSmallInputSet . Set.fromList <$> genListBetween 10 1000 arbitrary

-- data Authority
--   = AuthKeys (KeyPair 'Witness C_Crypto)
--   | AuthData (Data A)
--   --  AuthScript (Script A)
--   deriving (Show)

-- findKey :: KeySpace -> KeyHash 'Witness C_Crypto -> KeyPair 'Witness C_Crypto
-- findKey (KeySpace ks) target = snd . head $ filter (\(kh, _) -> kh == target) ks

-- instance Arbitrary KeySpace where
--   arbitrary = do
--     kps <- genListBetween 10 1000 arbitrary
--     pure $ KeySpace [(hashKey $ vKey kp, kp) | kp <- kps]

elementsT :: (Monad (t Gen), MonadTrans t) => [t Gen b] -> t Gen b
elementsT [] = error "Need at least one generator"
elementsT gens = do
  i <- lift $ choose (0, length gens - 1)
  gens !! i

data GenEnv = GenEnv
  { geValidityInterval :: ValidityInterval,
    gePParams :: PParams A
  }

data GenState = GenState
  { gsKeys :: Map (KeyHash 'Witness C_Crypto) (KeyPair 'Witness C_Crypto),
    gsScripts :: Map (ScriptHash C_Crypto) (Script A),
    gsDatums :: Map (DataHash C_Crypto) (Data A)
  }

instance Semigroup GenState where
  ts1 <> ts2 =
    GenState
      (gsKeys ts1 <> gsKeys ts2)
      (gsScripts ts1 <> gsScripts ts2)
      (gsDatums ts1 <> gsDatums ts2)

instance Monoid GenState where
  mempty = GenState mempty mempty mempty

type GenRS = RWST GenEnv () GenState Gen

getTxWitness :: TxBody A -> Int -> TxOut A -> GenRS (TxWitness A)
getTxWitness txBody txIx (TxOut addr _ mdh) = do
  let bodyHash = hashAnnotated txBody
  case addr of
    AddrBootstrap baddr ->
      error $ "Can't authorise bootstarp address: " ++ show baddr
    Addr _ payCred stakeCred -> do
      GenState {gsKeys, gsScripts, gsDatums} <- get
      let mkWitVKey :: Credential kr C_Crypto -> Gen (TxWitness A)
          mkWitVKey (KeyHashObj keyHash) =
            pure $
              mempty
                { txwitsVKey =
                    Set.singleton $
                      makeWitnessVKey bodyHash $
                        getByHash "credential" (coerceKeyRole keyHash) gsKeys
                }
          mkWitVKey (ScriptHashObj scriptHash) =
            let script = getByHash "script" scriptHash gsScripts
                scriptWit = mempty {txscripts = Map.singleton scriptHash script}
             in case script of
                  TimelockScript timelock -> do
                    timelockWit <- mkTimelockWit timelock
                    pure $ timelockWit <> scriptWit
                  PlutusScript _ps -> pure scriptWit
          mkTimelockWit =
            \case
              RequireSignature keyHash -> mkWitVKey (KeyHashObj keyHash)
              RequireAllOf timelocks -> F.fold <$> mapM mkTimelockWit timelocks
              RequireAnyOf timelocks
                | F.null timelocks -> pure mempty
                | otherwise -> mkTimelockWit =<< elements (F.toList timelocks)
              RequireMOf m timelocks -> do
                ts <- take m <$> shuffle (F.toList timelocks)
                F.fold <$> mapM mkTimelockWit ts
              RequireTimeStart _ -> pure mempty
              RequireTimeExpire _ -> pure mempty
          mkStakeWit (StakeRefBase cred) = mkWitVKey cred
          mkStakeWit _ = pure mempty
          mDatumWithHash = (\dh -> (dh, getByHash "datum" dh gsDatums)) <$> mdh
          datumWit =
            mempty
              { txdats =
                  TxDats $ strictMaybe mempty (uncurry Map.singleton) mDatumWithHash
              }
          mkRedeemerWit d = do
            GenEnv {gePParams} <- ask
            let rPtr = RdmrPtr Spend (fromIntegral txIx)
            --maxTxExUnit
            exUnits <- pure $ ExUnits 0 0 --lift arbitrary
            pure $ mempty {txrdmrs = Redeemers $ Map.singleton rPtr (d, exUnits)}
      witVKey <- lift $ mkWitVKey payCred
      stakeWitVKey <- lift $ mkStakeWit stakeCred
      redeemerWit <- strictMaybe (pure mempty) (mkRedeemerWit . snd) mDatumWithHash
      pure $ witVKey <> stakeWitVKey <> datumWit <> redeemerWit
  where
    getByHash :: (Ord k, Show k) => String -> k -> Map.Map k v -> v
    getByHash name k m =
      case Map.lookup k m of
        Nothing ->
          error $
            "Impossible: Can't find "
              ++ name
              ++ " in the test enviroment: "
              ++ show k
        Just val -> val

genCredential :: GenRS (KeyHash 'Witness C_Crypto)
genCredential = do
  keyPair <- lift arbitrary
  let keyHash = hashKey $ vKey keyPair
  modify $ \ts@GenState {gsKeys} -> ts {gsKeys = Map.insert keyHash keyPair gsKeys}
  pure keyHash

genTimelock :: GenRS (Timelock C_Crypto)
genTimelock = do
  GenEnv {geValidityInterval = ValidityInterval mBefore mAfter} <- ask
  -- We need to limit how deep these timelocks can go, otherwise this generator will
  -- diverge. It also has to stay very shallow because it grows too fast.
  let genNestedTimelock k
        | k > 0 =
          elementsT $
            nonRecTimelocks ++ [requireAllOf k, requireAnyOf k, requireMOf k]
        | otherwise = elementsT nonRecTimelocks
      nonRecTimelocks =
        [ r
          | SJust r <-
              [ SJust requireSignature,
                requireTimeStart <$> mBefore,
                requireTimeExpire <$> mAfter
              ]
        ]
      requireSignature = RequireSignature <$> genCredential
      requireAllOf k = do
        NonNegative (Small n) <- lift arbitrary
        RequireAllOf . Seq.fromList <$> replicateM n (genNestedTimelock (k - 1))
      requireAnyOf k = do
        Positive (Small n) <- lift arbitrary
        RequireAnyOf . Seq.fromList <$> replicateM n (genNestedTimelock (k - 1))
      requireMOf k = do
        NonNegative (Small n) <- lift arbitrary
        m <- lift $ choose (0, n)
        RequireMOf m . Seq.fromList <$> replicateM n (genNestedTimelock (k - 1))
      requireTimeStart (SlotNo validFrom) = do
        minSlotNo <- lift $ choose (minBound, validFrom)
        pure $ RequireTimeStart (SlotNo minSlotNo)
      requireTimeExpire (SlotNo validTill) = do
        maxSlotNo <- lift $ choose (validTill, maxBound)
        pure $ RequireTimeExpire (SlotNo maxSlotNo)
  genNestedTimelock (2 :: Natural)

genScript :: GenRS (StrictMaybe (DataHash C_Crypto), ScriptHash C_Crypto)
genScript =
  elementsT
    [ genScriptHash False . TimelockScript =<< genTimelock,
      genScriptHash True =<< genPlutusScript
    ]
  where
    genPlutusScript = alwaysSucceeds <$> lift arbitrary
    genScriptHash requireDatum script = do
      let scriptHash = hashScript @A script
      modify $ \ts@GenState {gsScripts} -> ts {gsScripts = Map.insert scriptHash script gsScripts}
      --shouldHaveDatum <- (requireDatum ||) <$> lift arbitrary
      mDatumHash <-
        if requireDatum
          then SJust <$> genDatumHash
          else pure SNothing
      pure (mDatumHash, scriptHash)

genPaymentCredential :: GenRS (StrictMaybe (DataHash C_Crypto), Credential 'Payment C_Crypto)
genPaymentCredential =
  elementsT
    [ do
        cred <- coerceKeyRole . KeyHashObj <$> genCredential
        -- mDatumHash <- elementsT [pure SNothing, SJust <$> genDatumHash]
        -- pure (mDatumHash, cred),
        pure (SNothing, cred),
      fmap ScriptHashObj <$> genScript
    ]

genStakingCredential :: GenRS (Credential 'Staking C_Crypto)
genStakingCredential = coerceKeyRole . KeyHashObj <$> genCredential

genRecipient :: GenRS (StrictMaybe (DataHash C_Crypto), Addr C_Crypto)
genRecipient = do
  (mDatumHash, paymentCred) <- genPaymentCredential
  stakeCred <- StakeRefBase <$> genStakingCredential
  pure (mDatumHash, Addr Testnet paymentCred stakeCred)

genDatumHash :: GenRS (DataHash C_Crypto)
genDatumHash = do
  datum <- lift arbitrary
  let datumHash = hashData datum
  modify $ \ts@GenState {gsDatums} -> ts {gsDatums = Map.insert datumHash datum gsDatums}
  pure datumHash

genTxOut :: Value A -> GenRS (TxOut A)
genTxOut val = do
  (mDatumHash, addr) <- genRecipient
  pure $ TxOut addr val mDatumHash

genUTxO :: GenRS (UTxO A)
genUTxO = do
  NonEmpty ins <- lift $ resize 10 arbitrary
  UTxO <$> sequenceA (Map.fromSet (const genOut) (Set.fromList ins))
  where
    genOut = genTxOut . inject . Coin . getNonNegative =<< lift arbitrary

genUTxOState :: UTxO A -> GenRS (UTxOState A)
genUTxOState utxo =
  lift (UTxOState utxo <$> arbitrary <*> arbitrary <*> pure def)

genRecipientsFrom :: [TxOut A] -> GenRS [TxOut A]
genRecipientsFrom txOuts = do
  let outCount = length txOuts
  approxCount <- lift $ choose (1, outCount)
  let extra = outCount - approxCount
      avgExtra = ceiling (toInteger extra % toInteger approxCount)
      genExtra e
        | e <= 0 || avgExtra == 0 = pure 0
        | otherwise = lift $ chooseInt (0, avgExtra)
  let goNew _ [] rs = pure rs
      goNew e (tx : txs) rs = do
        leftToAdd <- genExtra e
        goExtra (e - leftToAdd) leftToAdd (inject (Coin 0)) tx txs rs
      goExtra _ _ s tx [] rs = (++ rs) <$> genWithChange s tx
      goExtra e 0 s tx txs rs = do
        r <- genWithChange s tx
        goNew e txs (r ++ rs)
      goExtra e n s (TxOut _ v _) (tx : txs) rs =
        goExtra e (n - 1) (s <+> v) tx txs rs
      genWithChange s (TxOut addr v d) = do
        c <- Coin <$> lift (choose (0, unCoin $ coin v))
        r <- genTxOut (s <+> inject c)
        if c < coin v
          then
            let change = TxOut addr (v <-> inject c) d
             in pure [r, change]
          else pure [r]
  goNew extra txOuts []

genValidatedTx :: GenRS (UTxO A, ValidatedTx A)
genValidatedTx = do
  utxo <- genUTxO
  n <- lift $ choose (1, length (unUTxO utxo))
  toSpend <- Map.fromList . take n <$> lift (shuffle $ Map.toList $ unUTxO utxo)
  recipients <- genRecipientsFrom $ Map.elems toSpend
  nid <- lift $ elements [SNothing, SJust Testnet]
  GenEnv {geValidityInterval} <- ask
  let txIns = Map.keysSet toSpend
      txBody =
        TxBody
          { inputs = txIns,
            collateral = mempty,
            outputs = Seq.fromList recipients,
            txcerts = mempty,
            txwdrls = Wdrl mempty,
            txfee = Coin 0,
            txvldt = geValidityInterval,
            txUpdates = SNothing,
            reqSignerHashes = mempty,
            mint = mempty,
            scriptIntegrityHash = SNothing,
            adHash = SNothing,
            txnetworkid = nid
          }
  wits <- zipWithM (getTxWitness txBody) [0 ..] $ map snd $ Map.toAscList toSpend
  pure (utxo, ValidatedTx txBody (mconcat wits) (IsValid True) SNothing)

genTxAndUTXOState :: Gen (TRC (AlonzoUTXOW A))
genTxAndUTXOState = do
  maxTxExUnits <- arbitrary
  let genT = do
        (utxo, tx) <- genValidatedTx
        utxoState <- genUTxOState utxo
        pure $ TRC (utxoEnv, utxoState, tx)
      pp :: PParams A
      pp =
        def
          { _costmdls = Map.singleton PlutusV1 $ CostModel $ 0 <$ fromJust defaultCostModelParams,
            _maxValSize = 1000,
            _maxTxSize = fromIntegral (maxBound :: Int),
            _maxTxExUnits = maxTxExUnits,
            _collateralPercentage = 0
          }
      slotNo = SlotNo 100000000
      utxoEnv = UtxoEnv slotNo pp mempty (GenDelegs mempty)
  minSlotNo <- oneof [pure SNothing, SJust <$> choose (minBound, unSlotNo slotNo)]
  maxSlotNo <- oneof [pure SNothing, SJust <$> choose (unSlotNo slotNo + 1, maxBound)]
  let env =
        GenEnv
          { geValidityInterval = ValidityInterval (SlotNo <$> minSlotNo) (SlotNo <$> maxSlotNo),
            gePParams = pp
          }
  fst <$> evalRWST genT env mempty

totalAda :: UTxOState A -> Coin
totalAda (UTxOState utxo f d _) = f <> d <> coin (balance utxo)

testTxValidForUTXOW :: TRC (AlonzoUTXOW A) -> Property
testTxValidForUTXOW trc@(TRC (UtxoEnv _ pp _ _, utxoState, vtx)) =
  case runShelleyBase $ applySTSTest trc of
    Right utxoState' ->
      conjoin
        [ totalAda utxoState' === totalAda utxoState,
          minfee pp vtx === evaluateTransactionFee pp vtx 0,
          let vtxNoWits = vtx {wits = mempty}
              vtxCount = fromIntegral (length (txwitsVKey (wits vtx)))
           in minfee pp vtx === evaluateTransactionFee pp vtxNoWits vtxCount
        ]
    Left e -> counterexample (show e) (property False)

testValidTxForUTXOW :: Property
testValidTxForUTXOW = forAll genTxAndUTXOState testTxValidForUTXOW

alonzoProperties :: TestTree
alonzoProperties =
  testGroup
    "Alonzo UTXOW property tests"
    [ testProperty "test ValidTx" testValidTxForUTXOW
    ]
