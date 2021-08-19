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
    hashScriptIntegrity,
    minfee,
  )
import Cardano.Ledger.Alonzo.TxBody (TxBody (..), TxOut (..))
import Cardano.Ledger.Alonzo.TxWitness (RdmrPtr (..), Redeemers (..), TxDats (..), TxWitness (..))
import Cardano.Ledger.BaseTypes (Network (Testnet), StrictMaybe (..))
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Hashes (ScriptHash (..))
import Cardano.Ledger.Keys
  ( GenDelegs (..),
    KeyHash (..),
    KeyPair (..),
    KeyRole (..),
    coerceKeyRole,
    hashKey,
  )
import Cardano.Ledger.SafeHash (hashAnnotated)
import Cardano.Ledger.ShelleyMA.Timelocks (Timelock (..), ValidityInterval (..))
import Cardano.Ledger.Val
import Cardano.Slotting.Slot (SlotNo (..))
import Control.Monad (replicateM)
import Control.Monad.State.Strict (MonadState (..), modify)
import Control.Monad.Trans.Class (MonadTrans (lift))
import Control.Monad.Trans.RWS.Strict (RWST (..), ask, evalRWST)
import Control.State.Transition.Extended hiding (Assertion)
import Data.Default.Class (Default (def))
import qualified Data.Foldable as F
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Monoid (All (..))
import Data.Ratio ((%))
import qualified Data.Sequence.Strict as Seq
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
import Test.Shelley.Spec.Ledger.Utils (applySTSTest, runShelleyBase)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)

type A = AlonzoEra C_Crypto

elementsT :: (Monad (t Gen), MonadTrans t) => [t Gen b] -> t Gen b
elementsT [] = error "Need at least one generator"
elementsT gens = do
  i <- lift $ choose (0, length gens - 1)
  gens !! i

getByHashM ::
  (MonadState s m, Ord k, Show k) => String -> k -> (s -> Map.Map k v) -> m v
getByHashM name k getMap = do
  m <- getMap <$> get
  case Map.lookup k m of
    Nothing ->
      error $
        "Can't find " ++ name ++ " in the test enviroment: " ++ show k
    Just val -> pure val

data GenEnv = GenEnv
  { geValidityInterval :: ValidityInterval,
    gePParams :: PParams A
  }

data GenState = GenState
  { gsKeys :: Map (KeyHash 'Witness C_Crypto) (KeyPair 'Witness C_Crypto),
    gsScripts :: Map (ScriptHash C_Crypto) (StrictMaybe IsValid, Script A),
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

genTxPlutusWitness :: Int -> DataHash C_Crypto -> GenRS (TxWitness A)
genTxPlutusWitness txIx datumHash = do
  datum <- getByHashM "datum" datumHash gsDatums
  let datumWit = mempty {txdats = TxDats $ Map.singleton datumHash datum}
  let mkRedeemerWit = do
        GenEnv {gePParams} <- ask
        let rPtr = RdmrPtr Spend (fromIntegral txIx)
        --maxTxExUnit
        exUnits <- pure $ ExUnits 0 0 --lift arbitrary
        pure $ mempty {txrdmrs = Redeemers $ Map.singleton rPtr (datum, exUnits)}
  redeemerWit <- mkRedeemerWit
  pure $ datumWit <> redeemerWit

genTxWitness :: TxBody A -> TxOut A -> GenRS (TxWitness A)
genTxWitness txBody (TxOut addr _ _) = do
  let bodyHash = hashAnnotated txBody
  case addr of
    AddrBootstrap baddr ->
      error $ "Can't authorize bootstarp address: " ++ show baddr
    Addr _ payCred stakeCred -> do
      let mkWitVKey :: Credential kr C_Crypto -> GenRS (TxWitness A)
          mkWitVKey (KeyHashObj keyHash) = do
            cred <- getByHashM "credential" (coerceKeyRole keyHash) gsKeys
            pure $
              mempty
                { txwitsVKey = Set.singleton $ makeWitnessVKey bodyHash cred
                }
          mkWitVKey (ScriptHashObj scriptHash) = do
            (_, script) <- getByHashM "script" scriptHash gsScripts
            let scriptWit = mempty {txscripts = Map.singleton scriptHash script}
            case script of
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
                | otherwise -> mkTimelockWit =<< lift (elements (F.toList timelocks))
              RequireMOf m timelocks -> do
                ts <- take m <$> lift (shuffle (F.toList timelocks))
                F.fold <$> mapM mkTimelockWit ts
              RequireTimeStart _ -> pure mempty
              RequireTimeExpire _ -> pure mempty
          mkStakeWit (StakeRefBase cred) = mkWitVKey cred
          mkStakeWit _ = pure mempty
      witVKey <- mkWitVKey payCred
      stakeWitVKey <- mkStakeWit stakeCred
      pure $ witVKey <> stakeWitVKey

-- where
--   getByHash :: (Ord k, Show k) => String -> k -> Map.Map k v -> v
--   getByHash name k m =
--     case Map.lookup k m of
--       Nothing ->
--         error $
--           "Impossible: Can't find "
--             ++ name
--             ++ " in the test enviroment: "
--             ++ show k
--       Just val -> val

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

genScript :: GenRS (ScriptHash C_Crypto)
genScript =
  elementsT
    [ toScriptHash . (,) SNothing . TimelockScript =<< genTimelock,
      toScriptHash =<< genPlutusScript
    ]
  where
    genPlutusScript = do
      isValid <- lift $ frequency [(20, pure False), (80, pure True)]
      -- Plutus scripts expect exactly 3 arguments to work properly.
      let script
            | isValid = alwaysSucceeds 3
            | otherwise = alwaysFails 3
      pure (SJust (IsValid isValid), script)
    toScriptHash s@(_, script) = do
      let scriptHash = hashScript @A script
      modify $ \ts@GenState {gsScripts} -> ts {gsScripts = Map.insert scriptHash s gsScripts}
      pure scriptHash

hasValidScript :: MonadState GenState m => Addr C_Crypto -> m (StrictMaybe IsValid)
hasValidScript (Addr _ (ScriptHashObj scriptHash) _) =
  fst <$> getByHashM "script" scriptHash gsScripts
hasValidScript _ = pure SNothing

genPaymentCredential :: GenRS (Credential 'Payment C_Crypto)
genPaymentCredential =
  elementsT
    [ coerceKeyRole . KeyHashObj <$> genCredential,
      ScriptHashObj <$> genScript
    ]

genStakingCredential :: GenRS (Credential 'Staking C_Crypto)
genStakingCredential = coerceKeyRole . KeyHashObj <$> genCredential

genRecipient :: GenRS (Addr C_Crypto)
genRecipient = do
  paymentCred <- genPaymentCredential
  stakeCred <- StakeRefBase <$> genStakingCredential
  pure (Addr Testnet paymentCred stakeCred)

genDatumHash :: GenRS (DataHash C_Crypto)
genDatumHash = fst <$> genDatum

genDatum :: GenRS (DataHash C_Crypto, Data A)
genDatum = do
  datum <- lift arbitrary
  let datumHash = hashData datum
  modify $ \ts@GenState {gsDatums} -> ts {gsDatums = Map.insert datumHash datum gsDatums}
  pure (datumHash, datum)

genTxOut :: Value A -> GenRS (TxOut A)
genTxOut val = do
  addr <- genRecipient
  mIsValid <- hasValidScript addr
  mDatumHash <- mapM (const genDatumHash) mIsValid
  pure $ TxOut addr val mDatumHash

genUTxO :: GenRS (UTxO A)
genUTxO = do
  NonEmpty ins <- lift $ resize 10 arbitrary
  UTxO <$> sequenceA (Map.fromSet (const genOut) (Set.fromList ins))
  where
    genOut = genTxOut . inject . Coin . getNonNegative =<< lift arbitrary

genCollateralUTxO :: Coin -> UTxO A -> GenRS (UTxO A, Map.Map (TxIn C_Crypto) (TxOut A))
genCollateralUTxO (Coin fee) (UTxO utxoMap) = do
  GenEnv {gePParams} <- ask
  let collPerc = _collateralPercentage gePParams
      collTotal = Coin (ceiling ((fee * toInteger collPerc) % 100))
  cred <- coerceKeyRole . KeyHashObj <$> genCredential
  stakeCred <- StakeRefBase <$> genStakingCredential
  let collTxOut =
        TxOut (Addr Testnet cred stakeCred) (inject collTotal) SNothing
      genCollTxIn = do
        txIn <- arbitrary
        if Map.member txIn utxoMap
          then genCollTxIn
          else pure txIn
  collTxIn <- lift genCollTxIn
  pure (UTxO (Map.insert collTxIn collTxOut utxoMap), Map.singleton collTxIn collTxOut)

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
  utxoNoCollateral <- genUTxO
  let fee = Coin 0
  n <- lift $ choose (1, length (unUTxO utxoNoCollateral))
  toSpendNoCollateral <-
    Map.fromList . take n
      <$> lift (shuffle $ Map.toList $ unUTxO utxoNoCollateral)
  (utxo, collMap) <- genCollateralUTxO fee utxoNoCollateral
  let toSpend = Map.union collMap toSpendNoCollateral
      allValid vs = IsValid $ getAll $ mconcat [All v | SJust (IsValid v) <- vs]
  isValid <-
    allValid
      <$> mapM
        hasValidScript
        [addr | TxOut addr _ (SJust _) <- Map.elems toSpendNoCollateral]
  recipients <- genRecipientsFrom $ Map.elems toSpendNoCollateral
  nid <- lift $ elements [SNothing, SJust Testnet]
  GenEnv {geValidityInterval, gePParams} <- ask
  redeemerWitsList <-
    sequence
      [ genTxPlutusWitness ix dh
        | (ix, (_, TxOut _ _ mdh)) <- zip [0 ..] (Map.toAscList toSpend),
          SJust dh <- [mdh]
      ]
  let txIns = Map.keysSet toSpend
      redeemerWits = mconcat redeemerWitsList
      mIntegrityHash =
        hashScriptIntegrity
          gePParams
          ( if null redeemerWitsList
              then Set.empty
              else Set.singleton PlutusV1
          )
          (txrdmrs redeemerWits)
          (txdats redeemerWits)
      txBody =
        TxBody
          { inputs = txIns,
            collateral = Map.keysSet collMap,
            outputs = Seq.fromList recipients,
            txcerts = mempty,
            txwdrls = Wdrl mempty,
            txfee = fee,
            txvldt = geValidityInterval,
            txUpdates = SNothing,
            reqSignerHashes = mempty,
            mint = mempty,
            scriptIntegrityHash = mIntegrityHash,
            adHash = SNothing,
            txnetworkid = nid
          }
  keyWits <- mapM (genTxWitness txBody) $ Map.elems toSpend
  pure
    ( utxo,
      ValidatedTx txBody (redeemerWits <> mconcat keyWits) isValid SNothing
    )

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
