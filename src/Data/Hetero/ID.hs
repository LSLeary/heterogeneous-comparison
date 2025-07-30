
-- --< Header >-- {{{

{-# LANGUAGE TypeFamilies, CPP #-}

#if MIN_VERSION_GLASGOW_HASKELL(9,8,1,0)
{-# LANGUAGE TypeAbstractions #-}
#endif

{- |

Description : Higher-kinded t'Data.Hetero.ID.ID's
Copyright   : (c) L. S. Leary, 2025

Higher-kinded t'ID's with 'HetEq' & 'HetOrd'.

-}

-- }}}

-- --< Exports & Imports >-- {{{

module Data.Hetero.ID (

  -- * ID
  ID, newID,

) where

-- base
import Unsafe.Coerce (unsafeCoerce)
import Data.Coerce (coerce)
import Data.Unique (Unique, newUnique)

-- deepseq
import Control.DeepSeq (NFData)

-- hashable
import Data.Hashable (Hashable(hash))

-- heterogeneous-comparison
import Data.Hetero.Role (RoleKind(Representational))
import Data.Hetero.Evidence.Exactly (Exactly(ReprEx))
import Data.Hetero.Evidence.AtLeast (AtLeast(AtLeast))
import Data.Hetero.Eq (HetEq(..))
import Data.Hetero.Ord (HetOrdering(..), HetOrd(..), defaultHEq)

-- }}}

-- --< ID >-- {{{

-- | Higher-kinded t'ID's with 'HetEq' & 'HetOrd'.
type role ID representational
newtype   ID a where
  ID :: forall {k} (a :: k). Unique -> ID a
  deriving (Eq, Ord, NFData, Hashable)

instance HetEq ID where
  type Strength ID = Representational
  heq = defaultHEq

instance HetOrd ID where
  ID @a u1 `hcompare` ID @b u2 = case u1 `compare` u2 of
    LT -> HLT
    EQ -> HEQ (AtLeast magic)
    GT -> HGT
   where
    magic :: Exactly Representational a b
    magic = unsafeCoerce (ReprEx @a @a)

instance Show (ID a) where
  showsPrec _ i = showString "<ID:" . showsPrec 0 (hash i) . showChar '>'

-- | Create a new @t'ID' a@.
newID :: IO (ID a)
newID = coerce newUnique

-- }}}

