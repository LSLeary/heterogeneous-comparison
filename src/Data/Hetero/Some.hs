
-- --< Header >-- {{{

{-# LANGUAGE PatternSynonyms, QuantifiedConstraints #-}

{- |

Description : An (almost) drop-in replacement for "Data.Some" with broader 'Eq' & 'Ord'
Copyright   : (c) L. S. Leary, 2025

An (almost) drop-in replacement for "Data.Some".

=== Differences

 * Broader 'Eq' and 'Ord' instances via 'HetEq' and 'HetOrd', which generalise @GEq@ and @GCompare@ respectively.
 * No @GShow@ or @GNFData@ classes for 'Show' and 'NFData'; it suffices to wield @QuantifiedConstraints@.
 * 'Hashable' instance using the same approach.
 * For simplicity, 'Read' is neglected.

-}

-- }}}

-- --< Exports & Imports >-- {{{

module Data.Hetero.Some (

  -- * Some
  Some(Some),
  mkSome,
  withSome,
  withSomeM,
  mapSome,
  foldSome,
  traverseSome,

) where

-- GHC/base
import GHC.Exts (Any)

-- base
import Unsafe.Coerce (unsafeCoerce)

-- deepseq
import Control.DeepSeq (NFData(..))

-- hashable
import Data.Hashable (Hashable(..))

-- heterogeneous-comparison
import Data.Hetero.Eq (HetEq(..))
import Data.Hetero.Ord (HetOrdering(..), HetOrd(..))

-- }}}

-- --< Some >-- {{{

-- | Existentials sans indirection.
newtype Some f = UnsafeSome (f Any)

{-# COMPLETE Some #-}
pattern Some :: f x -> Some f
pattern Some fx <- UnsafeSome fx
  where Some fx = mkSome fx

instance HetEq f => Eq (Some f) where
  Some fx == Some fy = case fx `heq` fy of
    Nothing -> False
    Just _  -> True

instance HetOrd f => Ord (Some f) where
  Some fx `compare` Some fy = case fx `hcompare` fy of
    HLT   -> LT
    HEQ _ -> EQ
    HGT   -> GT

instance Applicative f => Semigroup (Some f) where
  UnsafeSome fAny1 <> UnsafeSome fAny2 = UnsafeSome (fAny1 *> fAny2)

instance Applicative f => Monoid (Some f) where
  mempty = Some (pure ())

instance (forall x. Show (f x)) => Show (Some f) where
  showsPrec d (Some fx)
    = showParen (d >= 11)
    $ showString "Some " . showsPrec 11 fx

instance (forall x. NFData (f x)) => NFData (Some f) where
  rnf = foldSome rnf

instance (forall x. Hashable (f x), HetEq f) => Hashable (Some f) where
  hash           = foldSome  hash
  hashWithSalt s = foldSome (hashWithSalt s)

mkSome :: f x -> Some f
mkSome = UnsafeSome . unsafeCoerce

withSome :: Some f -> (forall x. f x -> r) -> r
withSome (UnsafeSome fAny) k = k fAny

withSomeM :: Monad m => m (Some f) -> (forall x. f x -> m r) -> m r
withSomeM msf k = msf >>= foldSome k

mapSome :: (forall x. f x -> g x) -> Some f -> Some g
mapSome fg (UnsafeSome fAny) = UnsafeSome (fg fAny)

foldSome :: (forall x. f x -> b) -> Some f -> b
foldSome alg sf = withSome sf alg

traverseSome
  :: Applicative h
  => (forall x. f x -> h (g x)) -> Some f -> h (Some g)
traverseSome fhg (UnsafeSome fAny) = UnsafeSome <$> fhg fAny

-- }}}

