{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PartialTypeSignatures      #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

-- | Granna smart contracts
module Granna.Contract where


import Control.Monad hiding (fmap)
import Data.Aeson (FromJSON, ToJSON)
import qualified Data.Map as Map
import Data.Monoid (Last (..))
import Data.Text (Text)
import GHC.Generics (Generic)
import Ledger hiding (singleton)
import Ledger.Tx
import Plutus.ChainIndex.Tx (ChainIndexTx (..))
import Plutus.Contract as Contract
import qualified PlutusTx
import qualified PlutusTx.Builtins as Builtins
import PlutusTx.Prelude hiding (Semigroup (..), unless)
-- import           Ledger.Contexts
import Ledger.Ada as Ada
import Ledger.Constraints as Constraints
import Ledger.Scripts (validatorHash)
import qualified Ledger.Typed.Scripts as Scripts
import Ledger.Value as Value
-- import Plutus.Contracts.Currency as Currency
import Prelude (Semigroup (..), Show (..), String)
import qualified Prelude as Haskell
import           Plutus.Trace.Emulator (EmulatorTrace)
import qualified Plutus.Trace.Emulator as Trace
import           Plutus.Contract.Trace as X

{-
    General datatypes and functions
-}

data PrivateBlockHeader = PrivateBlockHeader
    { prevBlockHash :: !BuiltinByteString
    , merkleRoot    :: !BuiltinByteString
    } deriving stock (Generic, Haskell.Show, Haskell.Eq)

PlutusTx.makeLift ''PrivateBlockHeader
PlutusTx.unstableMakeIsData ''PrivateBlockHeader

{-
    Validator script
-}

data GrannaDatum = GrannaDatum
  { privBlockHeader :: !PrivateBlockHeader
  , threadOwner     :: !PubKeyHash
  } deriving stock (Generic, Haskell.Show, Haskell.Eq)

PlutusTx.makeLift ''GrannaDatum
PlutusTx.unstableMakeIsData ''GrannaDatum

data Granna
instance Scripts.ValidatorTypes Granna where
  type instance DatumType Granna = GrannaDatum
  type instance RedeemerType Granna = ()

{-# INLINABLE headerHash #-}
headerHash :: PrivateBlockHeader -> BuiltinByteString
headerHash (PrivateBlockHeader pbh mr) = sha2_256 $ Builtins.appendByteString pbh mr

{-# INLINABLE valsSentToScript #-}
valsSentToScript :: ValidatorHash -> TxInfo -> Maybe (GrannaDatum, Value)
valsSentToScript valHash txinfo = do
  (dHash, val) <- listToMaybe $ scriptOutputsAt valHash txinfo
  datum        <- findDatum dHash txinfo
  typedDatum   <- PlutusTx.fromBuiltinData $ getDatum datum
  return (typedDatum, val)

{-# INLINABLE grannaValidatorFunc #-}
grannaValidatorFunc :: GrannaDatum -> () -> ScriptContext -> Bool
grannaValidatorFunc prevDatum _ ctx@ScriptContext{scriptContextTxInfo=txinfo} =
  let
    valHash = ownHash ctx
    origOwner = threadOwner prevDatum
    prevHeaderHash = headerHash $ privBlockHeader prevDatum

    spentByOwner =
      let v = txSignedBy txinfo origOwner
      in traceIfFalse "Spender does not own the chain thread" v

    continuesChainCorrectly = fromMaybe False $ do
      prevValue <- txOutValue . txInInfoResolved <$> findOwnInput ctx
      (nextDatum, nextValue) <- valsSentToScript valHash txinfo

      let nextPbh = prevBlockHash $ privBlockHeader nextDatum
          nextOwner = threadOwner nextDatum

          resendsSameToken =
            traceIfFalse "NFT does not go back to contract" $ prevValue == nextValue
          continuesBlockChain =
            traceIfFalse "Invalid previous block header hash" $ prevHeaderHash == nextPbh
          sameOwner =
            traceIfFalse "Attempt to change private chain owner" $ origOwner == nextOwner

      return $ resendsSameToken && continuesBlockChain && sameOwner

  in spentByOwner && continuesChainCorrectly

typedGrannaValidator :: Scripts.TypedValidator Granna
typedGrannaValidator = Scripts.mkTypedValidator @Granna
    $$(PlutusTx.compile [|| grannaValidatorFunc ||])
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @GrannaDatum @()

grannaValidator :: Scripts.Validator
grannaValidator = Scripts.validatorScript typedGrannaValidator

grannaHash :: ValidatorHash
grannaHash = validatorHash grannaValidator

grannaAddress :: Address
grannaAddress = scriptAddress grannaValidator

{-
    NFT minting policy
-}

data DscpThreadCurrency = DscpThreadCurrency
    { dtcSpentOutput  :: (TxId, Integer)
    , dtcContractHash :: ValidatorHash
    } deriving stock (Generic, Haskell.Show, Haskell.Eq)

PlutusTx.makeLift ''DscpThreadCurrency

mkDscpThread :: TxOutRef -> DscpThreadCurrency
mkDscpThread (TxOutRef h i) = DscpThreadCurrency (h, i) grannaHash

{-# INLINABLE dscpTokenName #-}
dscpTokenName :: TokenName
dscpTokenName = TokenName "GRNN"

{-# INLINABLE mkPolicy #-}
mkPolicy :: DscpThreadCurrency -> () -> ScriptContext -> Bool
mkPolicy dtc _ ctx@ScriptContext{scriptContextTxInfo=txinfo} =
    let
      (h, i)  = dtcSpentOutput dtc
      valHash = dtcContractHash dtc

      spendsTxOut =
        let v = spendsOutput txinfo h i
        in traceIfFalse "Pending transaction does not spend a designated output" v

      ownSymbol = ownCurrencySymbol ctx
      minted = txInfoMint txinfo
      expected = Value.singleton ownSymbol dscpTokenName 1

      mintsToken =
        let v = expected == minted
        in traceIfFalse "Invalid minted value" v

      sendsCorrectlyToScript =
        let v = case valsSentToScript valHash txinfo of
              Nothing -> False
              Just (GrannaDatum {..}, val) ->
                txSignedBy txinfo threadOwner &&  -- it's signed by the owner of pubkey in the datum
                val == expected                   -- it sends the token just minted to the script
        in traceIfFalse "Minted token with correct data is not sent to Granna script" v

    in spendsTxOut && mintsToken && sendsCorrectlyToScript

policy :: DscpThreadCurrency -> Scripts.MintingPolicy
policy dtc = mkMintingPolicyScript $
  $$(PlutusTx.compile [|| Scripts.wrapMintingPolicy . mkPolicy ||])
  `PlutusTx.applyCode`
  PlutusTx.liftCode dtc

curSymbol :: DscpThreadCurrency -> CurrencySymbol
curSymbol = scriptCurrencySymbol . policy

{-
  Off-chain code
-}

type GrannaSchema =
  Endpoint "startChain" ()
  .\/ Endpoint "submitBlock" BuiltinByteString
  .\/ Endpoint "validateHeader" (TxId, BuiltinByteString)


startChain :: Promise () GrannaSchema Text ()
startChain = endpoint @"startChain" $ \_ -> do
  pkHash <- Contract.ownPubKeyHash
  utxos <- utxosAt $ pubKeyHashAddress pkHash
  case Map.keys utxos of
    []       -> Contract.logError @String "no utxo found"
    oref : _ -> do
      let dtc     = mkDscpThread oref
          val     = Value.singleton (curSymbol dtc) dscpTokenName 1
          genHead = PrivateBlockHeader "" ""
          datum   = GrannaDatum genHead pkHash

          lookups = Constraints.mintingPolicy (policy dtc) <>
                    Constraints.typedValidatorLookups typedGrannaValidator <>
                    Constraints.unspentOutputs utxos
          tx      = Constraints.mustMintValue val <>
                    Constraints.mustSpendPubKeyOutput oref <>
                    Constraints.mustPayToTheScript datum val

      ledgerTx <- submitTxConstraintsWith @Granna lookups tx
      void $ awaitTxConfirmed $ getCardanoTxId ledgerTx

submitBlock :: Promise () GrannaSchema Text ()
submitBlock = endpoint @"submitBlock" $ \mrkRoot -> do
  pkHash <- Contract.ownPubKeyHash
  scriptUtxos <- utxosAt grannaAddress
  case Map.assocs scriptUtxos of
    -- TBD This is a toy example which assumes that there is only one producer;
    -- real off-chain code will not assume that and will instead remember
    -- the last UTxO from the private chain in the application memory
    [(oref, ScriptChainIndexTxOut { _ciTxOutDatum = (Right rawDatum), _ciTxOutValue = val })] ->
      let GrannaDatum{privBlockHeader=pbh} =
            fromMaybe (error ()) $
            PlutusTx.fromBuiltinData $ getDatum rawDatum
          prevBlockHash = headerHash pbh
          newHead  = PrivateBlockHeader
            { prevBlockHash = prevBlockHash
            , merkleRoot    = mrkRoot
            }
          newDatum = GrannaDatum newHead pkHash

          tx = Contract.collectFromScript scriptUtxos () <>
               Constraints.mustPayToTheScript newDatum val
      in do
        ledgerTx <- submitTxConstraintsSpending typedGrannaValidator scriptUtxos tx
        void $ awaitTxConfirmed $ getCardanoTxId ledgerTx

    _ -> Contract.logError @String "script address has no valid utxo"

validateHeader :: Promise () GrannaSchema Text ()
validateHeader = endpoint @"validateHeader" $ \(txid, mrkRoot) -> txFromTxId txid >>= \case
  Nothing ->
    Contract.logError @String "INVALID: no transaction found"
  Just ChainIndexTx{_citxData=datums} -> do
    let (rawDatum:_) = Map.elems datums
        GrannaDatum{privBlockHeader=pbh} =
          fromMaybe (error ()) $
          PlutusTx.fromBuiltinData $ getDatum rawDatum
    if mrkRoot == merkleRoot pbh
      then Contract.logInfo @String "VALID: all good"
      else Contract.logError @String $ "INVALID: bad merkle root, expected " ++ show (merkleRoot pbh) ++ ", got " ++ show mrkRoot

endpoints :: Contract () GrannaSchema Text ()
endpoints = selectList [startChain, submitBlock, validateHeader] >> endpoints

submitTrace :: EmulatorTrace ()
submitTrace = do
  let w1 = X.knownWallet 1
      mrkRoot = "asfasdfsadfasdf" :: BuiltinByteString

  h1 <- Trace.activateContractWallet w1 startChain
  void $ Trace.waitNSlots 1
  Trace.callEndpoint @"startChain" h1 ()

  void $ Trace.waitNSlots 1
  Trace.callEndpoint @"submitBlock" h1 mrkRoot
  void $ Trace.waitNSlots 1
