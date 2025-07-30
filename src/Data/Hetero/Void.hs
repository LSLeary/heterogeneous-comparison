
-- --< Header >-- {{{

{-# LANGUAGE TypeFamilies #-}

{- |

Description : A higher-kinded t'Data.Void.Void'.
Copyright   : (c) L. S. Leary, 2025

A higher-kinded t'Data.Void.Void'.
Dual to t'Data.Proxy.Proxy'.

-}

-- }}}

-- --< Imports & Exports >-- {{{

module Data.Hetero.Void (

  -- * VoidF
  VoidF,
  absurdF,
  vacuousF,

) where

-- heterogeneous-comparison
import Data.Hetero.Role (RoleKind(Nominal))
import Data.Hetero.Eq (HetEq(..))
import Data.Hetero.Ord (HetOrd(..))

-- }}}

-- --< VoidF >-- {{{

-- | A higher-kinded t'Data.Void.Void'.
--   Dual to t'Data.Proxy.Proxy'.
data VoidF a
  deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

instance HetEq VoidF where
  type Strength VoidF = Nominal
  heq = \case{}

instance HetOrd VoidF where
  hcompare = \case{}

instance Semigroup (VoidF a) where
  (<>) = \case{}

absurdF :: VoidF a -> b
absurdF = \case{}

vacuousF :: Functor f => f (VoidF a) -> f b
vacuousF = fmap absurdF

-- }}}

