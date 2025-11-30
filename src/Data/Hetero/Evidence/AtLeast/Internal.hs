
-- TODO: merge back into Data.Hetero.Evidence.AtLeast

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

-- base
import Data.Type.Ord (Min)
import Control.Category (Category(..))

-- ord-axiomata
import Data.Type.Ord.Relations (type (<=))
import Data.Type.Ord.Axiomata (BoundedAbove(..), Proof(..))
import Data.Type.Ord.Lemmata (minMono)

-- heterogeneous-comparison
import Data.Hetero.Role (KnownRole(..))
import Data.Hetero.Evidence.Exactly (Exactly(..), hetTransEx, roleEx)

-- }}}

-- --< AtLeast >-- {{{

data AtLeast r a b where
  AtLeast :: r <= s => !(Exactly s a b) -> AtLeast r a b

-- }}}

-- --< AtLeast: Instances & Deps >-- {{{

instance KnownRole r => Category (AtLeast r) where
  id  = reflAL
  (.) = flip transAL

-- | Reflexivity.
reflAL :: forall r a. KnownRole r => AtLeast r a a
reflAL = case greatest (knownRole @r) of
  QED -> AtLeast NomEx

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
  QED -> AtLeast (hetTransEx e1 e2)
 where
  r = knownRole @r
  s = knownRole @s
  t = roleEx e1
  u = roleEx e2

-- }}}

