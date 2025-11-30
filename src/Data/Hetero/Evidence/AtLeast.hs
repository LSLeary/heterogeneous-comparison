
-- --< Header >-- {{{
{-#
LANGUAGE
  GADTs, PatternSynonyms, ExplicitNamespaces, QuantifiedConstraints
#-}

{- |

Description : Evidence t'Data.Hetero.Evidence.AtLeast.AtLeast' as strong as that t'Data.Hetero.Evidence.Exactly.Exactly' corresponding to a given t'Data.Hetero.Role.Role'
Copyright   : (c) L. S. Leary, 2025

Evidence t'AtLeast' as strong as that 'Exactly' corresponding to a given 'Data.Hetero.Role.Role'.

-}

-- }}}

-- --< Exports >-- {{{

module Data.Hetero.Evidence.AtLeast (

  -- * AtLeast
  AtLeast(AtLeast, PhantAL, ReprAL, NomAL),
  reflAL,
  symAL,
  transAL,
  hetTransAL,
  maxAL,
  weakenAL,
  weakenALToEx,
  innerAL,

) where

-- }}}

-- --< Imports >-- {{{

-- base
import Data.Type.Ord (Max)
import Data.Coerce (Coercible)

-- ord-axiomata
import Data.Type.Ord.Relations (type (<=))
import Data.Type.Ord.Axiomata (TotalOrder(..), Proof(..))
import Data.Type.Ord.Lemmata (maxMono)

-- heterogeneous-comparison
import Data.Hetero.Role (RoleKind(..), KnownRole(..), SuperPhantom)
import Data.Hetero.Evidence.Exactly
  (Exactly(..), symEx, maxEx, roleEx, weakenEx, innerEx)
import Data.Hetero.Evidence.AtLeast.Internal

-- }}}

-- --< AtLeast >-- {{{

{-# INLINE PhantAL #-}
{-# INLINE ReprAL  #-}
{-# INLINE NomAL   #-}
{-# COMPLETE PhantAL, ReprAL, NomAL #-}
pattern PhantAL
  :: () =>  r <= Phantom                            => AtLeast r a b
pattern ReprAL
  :: () => (r <= Representational, a `Coercible` b) => AtLeast r a b
pattern NomAL
  :: () => (r <= Nominal         , a      ~      b) => AtLeast r a b
pattern PhantAL = AtLeast PhantEx
pattern ReprAL  = AtLeast ReprEx
pattern NomAL   = AtLeast NomEx

-- | Symmetry.
symAL :: AtLeast r a b -> AtLeast r b a
symAL (AtLeast ex) = AtLeast (symEx ex)

{- |

@t'AtLeast' _ a b@ is a monoid graded by the 'Max' monoid on 'RoleKind' with identity:

@
'PhantAL' :: t'AtLeast' t'Phantom' a b
@

-}
maxAL
  :: forall r s a b
  .  (KnownRole r, KnownRole s)
  => AtLeast r a b -> AtLeast s a b {- ^ -}
  -> AtLeast (Max r s) a b
maxAL (AtLeast e1) (AtLeast e2) = case mono of
  QED -> AtLeast (maxEx e1 e2)
 where
  mono = maxMono
    (knownRole @r) (knownRole @s)
    (roleEx e1) (roleEx e2)

-- | Weaken evidence for one 'Data.Hetero.Role.Role' to evidence for a lesser @Role@.
weakenAL
  :: forall r s a b
  .  (KnownRole r, KnownRole s, r <= s)
  => AtLeast s a b {- ^ -}
  -> AtLeast r a b
weakenAL (AtLeast e) = case trans of
  QED -> AtLeast e
 where
  trans = transLeq (knownRole @r) (knownRole @s) (roleEx e)

-- | Weaken inexact evidence to exact evidence of the same role.
weakenALToEx :: KnownRole r => AtLeast r a b -> Exactly r a b
weakenALToEx (AtLeast ex) = weakenEx ex

-- | If applications by @'SuperPhantom' f@ are equivalent, then so are the arguments.
innerAL
  :: SuperPhantom f
  => AtLeast r (f a) (f b) {- ^ -}
  -> AtLeast r a b
innerAL (AtLeast ex) = AtLeast (innerEx ex)

-- }}}

