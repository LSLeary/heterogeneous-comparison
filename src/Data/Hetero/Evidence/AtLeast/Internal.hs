
-- --< Header >-- {{{

{-#
LANGUAGE
  GADTs, DataKinds, PatternSynonyms, ViewPatterns,
  ExplicitNamespaces, UnboxedTuples
#-}

-- }}}

-- --< Exports >-- {{{

module Data.Hetero.Evidence.AtLeast.Internal (
  AtLeast(AtLeast),
  reflAL,
  transAL,
  hetTransAL,
) where

-- }}}

-- --< Imports >-- {{{

-- GHC/base
import GHC.Exts (Any)

-- base
import Prelude hiding (id, (.))
import Data.Type.Equality ((:~:)(..))
import Data.Type.Ord (Min)
import Control.Category (Category(..))
import Unsafe.Coerce (unsafeCoerce)

-- ord-axiomata
import Data.Type.Ord.Axiomata (type (<=), BoundedAbove(..), Proof)
import Data.Type.Ord.Lemmata (minMono)

-- heterogeneous-comparison
import Data.Hetero.Role (RoleKind, KnownRole(..))
import Data.Hetero.Evidence.Exactly (Exactly(..), hetTransEx, roleEx)

-- }}}

-- --< AtLeast >-- {{{

-- NOTE: This module provides what is morally
--
-- > data AtLeast r a b where
-- >   AtLeast :: r <= s => !(Exactly s a b) -> AtLeast r a b
--
-- but encoded as a newtype with a pattern synonym.
--
-- For an explanation of the techniques used, see:
--   https://gist.github.com/LSLeary/dd52b3086eb153e3c99e578f19eec1ee
--
-- In particular, the 'Existentials' and 'Equality Constaints' sections.

-- | Evidence @AtLeast@ as strong as that 'Exactly' corresponding to a given 'Data.Hetero.Role.Role'.
newtype AtLeast (r :: RoleKind) a b
  = UnsafeAtLeast{ extract :: Exactly Any a b }
type role AtLeast nominal nominal nominal
               -- ^^^^^^^ Necessary for soundness!

{-# INLINE view #-}
view :: AtLeast r a b -> (# Proof (r <= Any), Exactly Any a b #)
view !al = (# unsafeCoerce (Refl @True), extract al #)
  -- ^ Necessary for soundness!

{-# COMPLETE AtLeast #-}
{-# INLINE   AtLeast #-}
pattern AtLeast :: () => r <= s => Exactly s a b -> AtLeast r a b
pattern AtLeast x <- (view -> (# Refl, x #))
  where AtLeast x = UnsafeAtLeast (unsafeCoerce x)

-- }}}

-- --< AtLeast: Instances & Deps >-- {{{

instance Show (AtLeast r a b) where
  showsPrec d (AtLeast ex)
    = showParen (d >= 11)
    $ showString "AtLeast "
    . showsPrec 11 ex

instance Eq (AtLeast r a b) where
  AtLeast PhantEx == AtLeast PhantEx = True
  AtLeast ReprEx  == AtLeast ReprEx  = True
  AtLeast NomEx   == AtLeast NomEx   = True
  _               == _               = False

instance Ord (AtLeast r a b) where
  compare (AtLeast ex1) (AtLeast ex2) = case ex1 of
    PhantEx -> case ex2 of
      PhantEx -> EQ
      _       -> LT
    ReprEx  -> case ex2 of
      PhantEx -> GT
      ReprEx  -> EQ
      NomEx   -> LT
    NomEx   -> case ex2 of
      NomEx   -> EQ
      _       -> GT

instance KnownRole r => Category (AtLeast r) where
  id  = reflAL
  (.) = flip transAL

-- | Reflexivity.
reflAL :: forall r a. KnownRole r => AtLeast r a a
reflAL = case greatest (knownRole @r) of
  Refl -> AtLeast NomEx

-- | 'Data.Hetero.Role.Role'-homogeneous transitivity.
transAL :: KnownRole r => AtLeast r a b -> AtLeast r b c -> AtLeast r a c
transAL = hetTransAL

{- |

t'AtLeast' is a category graded by the 'Min' monoid on 'RoleKind' with identity:

@
'Data.Hetero.Evidence.AtLeast.NomAL' :: t'AtLeast' t'Data.Hetero.Role.Nominal' a a
@

-}
hetTransAL
  :: forall r s a b c
  .  (KnownRole r, KnownRole s)
  => AtLeast r a b -> AtLeast s b c {- ^ -}
  -> AtLeast (Min r s) a c
hetTransAL (AtLeast e1) (AtLeast e2) = case minMono r s t u of
  Refl -> AtLeast (hetTransEx e1 e2)
 where
  r = knownRole @r
  s = knownRole @s
  t = roleEx e1
  u = roleEx e2

-- }}}

