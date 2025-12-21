
-- --< Header >-- {{{

{-# LANGUAGE TypeFamilies, CPP #-}

#if MIN_VERSION_GLASGOW_HASKELL(9,8,1,0)
{-# LANGUAGE TypeAbstractions #-}
#endif

{- |

Description : t'Representational' 'ID's
Copyright   : (c) L. S. Leary, 2025

t'Representational' 'ID's with 'HetEq' & 'HetOrd'.

-}

-- }}}

-- --< Exports & Imports >-- {{{

module Data.Hetero.ID.Repr (

  -- * ID
  ID, newID,
  newIDIO,

  -- * Re-exports
  USG, runUSG,
  RealWorld

) where

-- base
import Unsafe.Coerce (unsafeCoerce)
import Type.Reflection (Typeable, typeRep)
import Data.Kind (Type)

-- deepseq
import Control.DeepSeq (NFData)

-- hashable
import Data.Hashable (Hashable(hash))

-- heterogeneous-comparison
import Data.Hetero.Role (RoleKind(Representational), Role(Representational))
import Data.Hetero.Evidence.Exactly (Exactly(ReprEx))
import Data.Hetero.Evidence.AtLeast (AtLeast(AtLeast))
import Data.Hetero.Eq (HetEq(..))
import Data.Hetero.Ord (HetOrdering(..), HetOrd(..), defaultHEq)
import Control.Monad.USG

-- }}}

-- --< ID >-- {{{

-- | t'Representational' 'ID's with 'HetEq' & 'HetOrd'.
type role ID    nominal representational
type      ID :: Type -> k -> Type
newtype   ID    s       a    where
  MkID :: forall {k} {s} (a :: k). Symbol s -> ID s a
  deriving
    ( Eq
    , Ord -- ^ Ordered by time of creation.
    , NFData
    , Hashable
    )

instance HetEq (ID s) where
  type Strength (ID s) = Representational
  heq = defaultHEq

-- | Ordered by time of creation.
instance HetOrd (ID s) where
  MkID @a s1 `hcompare` MkID @b s2 = case s1 `compare` s2 of
    LT -> HLT
    EQ -> HEQ (AtLeast magic)
    GT -> HGT
   where
    magic :: Exactly Representational a b
    magic = unsafeCoerce (ReprEx @a @a)

instance Typeable a => Show (ID s a) where
  showsPrec _ i
    = showString "<ID:"
    . showsPrec 0 (hash i)
    . showChar ','
    . showsPrec 0 Representational
    . showChar ','
    . showsPrec 0 (typeRep @a)
    . showChar '>'

-- | Create a new t'Representational' 'ID' for @a@ that's unique in the state thread @s@.
newID :: forall {s} a. USG s (ID s a)
newID = MkID <$> newSymbol

-- | Create a new t'Representational' 'ID' for @a@ that's unique in the @RealWorld@.
newIDIO :: IO (ID RealWorld a)
newIDIO = MkID <$> newSymbolIO

-- }}}

