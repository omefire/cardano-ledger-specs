{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Test.Cardano.Ledger.Properties where

--import Debug.Trace (trace)

--import Cardano.Ledger.Mary.Value (Value (..))

--ScriptPurpose (..),

--hashWitnessPPData,

--Positive (..),

import Cardano.Ledger.Alonzo (AlonzoEra)
import Cardano.Ledger.Alonzo.Data (Data, DataHash)
import Cardano.Ledger.Alonzo.Language (Language (..))
import Cardano.Ledger.Alonzo.PParams (PParams, PParams' (..))
import Cardano.Ledger.Alonzo.Rules.Utxow (AlonzoUTXOW)
import Cardano.Ledger.Alonzo.Scripts (CostModel (..))
import Cardano.Ledger.Alonzo.Tx
  ( IsValid (..),
    ValidatedTx (..),
    minfee,
  )
import Cardano.Ledger.Alonzo.TxBody (TxBody (..), TxOut (..))
import Cardano.Ledger.Alonzo.TxWitness (Redeemers (..), TxWitness (..))
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
import Cardano.Ledger.Val (coin, inject, (<->))
import Cardano.Slotting.Slot (SlotNo (..))
import Control.State.Transition.Extended hiding (Assertion)
import Data.ByteString.Short (ShortByteString)
import Data.Default.Class (Default (def))
import Data.List (nub, sort)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import qualified Data.Sequence.Strict as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Plutus.V1.Ledger.Api (defaultCostModelParams)
import Shelley.Spec.Ledger.API
  ( Addr (..),
    CLI (evaluateTransactionFee),
    Credential (..),
    StakeReference (..),
    TxIn,
    UTxO (..),
    Wdrl (..),
  )
import Shelley.Spec.Ledger.LedgerState (UTxOState (..))
import Shelley.Spec.Ledger.STS.Utxo (UtxoEnv (..))
import Shelley.Spec.Ledger.UTxO (balance, makeWitnessVKey)
import Test.Cardano.Ledger.Alonzo.Serialisation.Generators ()
import Test.QuickCheck
  ( Property,
    choose,
    chooseInt,
    conjoin,
    counterexample,
    elements,
    oneof,
    property,
    vectorOf,
    (===),
    (==>),
  )
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

newtype KeySpace = KeySpace [(KeyHash 'Witness C_Crypto, KeyPair 'Witness C_Crypto)]
  deriving (Show)

genListBetween :: Int -> Int -> Gen a -> Gen [a]
genListBetween a b g = chooseInt (a, b) >>= flip vectorOf g

data Vault a b = Vault
  { sid :: [a],
    sec :: Map a b
  }

data BagOSecrets = BagOSecrets
  { keys :: Vault (KeyHash 'Witness C_Crypto) (KeyPair 'Witness C_Crypto),
    timelocks :: Vault (ScriptHash C_Crypto) (Timelock A, [KeyPair 'Witness C_Crypto]),
    plutons :: Vault (ScriptHash C_Crypto) ShortByteString,
    datums :: Vault (DataHash C_Crypto) (Data A)
  }

findKey :: KeySpace -> KeyHash 'Witness C_Crypto -> KeyPair 'Witness C_Crypto
findKey (KeySpace ks) target = snd . head $ filter (\(kh, _) -> kh == target) ks

instance Arbitrary KeySpace where
  arbitrary = do
    kps <- genListBetween 10 1000 (mkKeyPair' <$> arbitrary)
    pure $ KeySpace [(hashKey $ vKey kp, kp) | kp <- kps]

genPaymentKeyCred ::
  KeySpace ->
  Gen (Credential 'Payment C_Crypto, StrictMaybe (DataHash C_Crypto))
genPaymentKeyCred (KeySpace ks) = do
  kp <- elements ks
  pure (coerceKeyRole . KeyHashObj . fst $ kp, SNothing)

genPaymentCred ::
  KeySpace ->
  Gen (Credential 'Payment C_Crypto, StrictMaybe (DataHash C_Crypto))
genPaymentCred ks = oneof [genPaymentKeyCred ks]

genStakeKeyCred :: KeySpace -> Gen (StakeReference C_Crypto)
genStakeKeyCred (KeySpace ks) =
  StakeRefBase . coerceKeyRole . KeyHashObj . fst <$> elements ks

genStakeCred :: KeySpace -> Gen (StakeReference C_Crypto)
genStakeCred ks = oneof [genStakeKeyCred ks]

genOut ::
  KeySpace ->
  Gen (TxOut A)
genOut ks = do
  (pc, dh) <- genPaymentCred ks
  sc <- genStakeCred ks
  c <- arbitrary
  pure $ TxOut @A (Addr Testnet pc sc) (inject c) dh

genUTxO :: Set (Data A) -> KeySpace -> Gen (UTxO A)
genUTxO _ds ks = do
  NotTooSmallInputSet ins <- arbitrary
  UTxO . Map.fromList
    <$> mapM (\i -> fmap (i,) (genOut ks)) (Set.toList ins)

genUTxOState :: UTxO A -> Gen (UTxOState A)
genUTxOState utxo = UTxOState utxo <$> arbitrary <*> arbitrary <*> pure def

pp :: PParams A
pp =
  def
    { _costmdls = Map.singleton PlutusV1 $ CostModel $ 0 <$ fromJust defaultCostModelParams,
      _maxValSize = 1000
    }

utxoEnv :: UtxoEnv A
utxoEnv = UtxoEnv (SlotNo 0) pp mempty (GenDelegs mempty)

data Authority
  = AuthKeys (KeyPair 'Witness C_Crypto)
  | AuthData (Data A)
  --  AuthScript (Script A)
  deriving (Show)

getAuth :: TxOut A -> KeySpace -> [Authority]
getAuth (TxOut (Addr _ (KeyHashObj kh) _) _ _) ks =
  [AuthKeys $ findKey ks (coerceKeyRole kh)]
getAuth _ _ = []

getAuths :: KeySpace -> [TxOut A] -> [Authority]
getAuths ks = foldr (\o as -> getAuth o ks ++ as) []

authorize :: TxBody A -> Authority -> TxWitness A -> TxWitness A
authorize txb (AuthKeys kp) ws =
  ws
    { txwitsVKey =
        Set.insert
          (makeWitnessVKey (hashAnnotated txb) kp)
          (txwitsVKey ws)
    }
authorize _ (AuthData _d) ws = ws

genTx ::
  UTxO A ->
  Set (Data A) ->
  KeySpace ->
  Gen (ValidatedTx A)
genTx utxo _ds ks = do
  (txin, txout) <- elements . Map.toList $ unUTxO utxo
  (pc, _) <- genPaymentCred ks
  sc <- genStakeCred ks
  let newAddr = Addr Testnet pc sc
      auth = getAuths ks [txout]
      (TxOut _ v _) = txout
  c <- choose (0, unCoin $ coin v)
  nid <- elements [SNothing, SJust Testnet]
  let v' = v <-> inject (Coin c)
      bdy =
        TxBody
          (Set.singleton txin)
          mempty -- collateral
          (Seq.singleton $ TxOut newAddr v' SNothing)
          mempty -- certs
          (Wdrl mempty)
          (Coin c)
          (ValidityInterval SNothing SNothing)
          SNothing -- updates
          mempty -- req signers
          mempty
          SNothing -- wppHash
          SNothing -- adHash
          nid
  pure $
    ValidatedTx
      bdy
      (foldr (authorize bdy) ewits auth)
      (IsValid True)
      SNothing
  where
    ewits = TxWitness mempty mempty mempty mempty (Redeemers Map.empty)

genTxAndUTXOState ::
  Set (Data A) ->
  KeySpace ->
  Gen (ValidatedTx A, UTxOState A)
genTxAndUTXOState ds ks = do
  utxo <- genUTxO ds ks
  utxoSt <- genUTxOState utxo
  tx <- genTx utxo ds ks
  pure (tx, utxoSt)

totalAda :: UTxOState A -> Coin
totalAda (UTxOState utxo f d _) = f <> d <> coin (balance utxo)

type UtxowReturn = Either [PredicateFailure (AlonzoUTXOW A)] (UTxOState A)

utxow :: ValidatedTx A -> UTxOState A -> UtxowReturn
utxow t u = runShelleyBase $ applySTSTest @(AlonzoUTXOW A) (TRC (utxoEnv, u, t))

testTxValidForUTXOW :: ValidatedTx A -> UTxOState A -> Property
testTxValidForUTXOW vtx utxoState =
  case utxow vtx utxoState of
    Right utxoState' ->
      conjoin
        [ totalAda utxoState' === totalAda utxoState,
          minfee pp vtx === evaluateTransactionFee pp vtx 0,
          let vtxNoWits = vtx {wits = mempty}
              vtxCount = fromIntegral (length (txwitsVKey (wits vtx)))
           in minfee pp vtx === evaluateTransactionFee pp vtxNoWits vtxCount
        ]
    Left e -> counterexample (show e) (property False)

newtype NotTooSmallInputSet = NotTooSmallInputSet (Set (TxIn C_Crypto))
  deriving (Show)

instance Arbitrary NotTooSmallInputSet where
  arbitrary = NotTooSmallInputSet . Set.fromList <$> genListBetween 10 1000 arbitrary

testValidTxForUTXOW :: Set (Data A) -> KeySpace -> Property
testValidTxForUTXOW ds ks =
  forAll (genTxAndUTXOState ds ks) (uncurry testTxValidForUTXOW)

alonzoProperties :: TestTree
alonzoProperties =
  testGroup
    "Alonzo UTXOW property tests"
    [ testProperty "test ValidTx" testValidTxForUTXOW
    ]
