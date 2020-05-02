{-# OPTIONS_GHC -Wno-orphans #-}

module Shelley.Spec.Ledger.Orphans where

import           Cardano.Prelude (NFData, NoUnexpectedThunks)
import           Data.IP (IPv4, IPv6)
import           Shelley.Spec.Ledger.Slot (SlotNo)

instance NFData SlotNo

instance NoUnexpectedThunks IPv4
instance NoUnexpectedThunks IPv6
