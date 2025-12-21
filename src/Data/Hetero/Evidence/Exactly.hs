
-- --< Header >-- {{{

{-# LANGUAGE GADTs, ExplicitNamespaces, QuantifiedConstraints #-}

{- |

Description : Evidence t'Data.Hetero.Evidence.Exactly.Exactly' corresponding to each t'Data.Hetero.Role.Role'
Copyright   : (c) L. S. Leary, 2025

Evidence 'Exactly' corresponding to each 'Role'.

-}

-- }}}

-- --< Exports >-- {{{

module Data.Hetero.Evidence.Exactly (

  -- * Exactly
  Exactly(..),
  roleEx,
  reflEx,
  symEx,
  transEx,
  hetTransEx,
  maxEx,
  weakenEx,
  applyEx,
  innerEx,

) where

-- }}}

-- --< Imports >-- {{{

-- base
import Prelude hiding (id, (.))
import Data.Type.Equality ((:~:)(..))
import Data.Type.Ord (OrderingI(..), Min, Max)
import Data.Coerce (Coercible)
import Control.Category (Category(..))

-- ord-axiomata
import Data.Type.Ord.Axiomata (type (<=), TotalOrder(..))

-- heterogeneous-comparison
import Data.Hetero.Role
  ( RoleKind(..), Role(..), KnownRole(..), expositRole
  , SubNominal, SuperPhantom
  )

-- }}}

-- --< Exactly >-- {{{

{- |

Evidence of equivalence, /exactly/ corresponding to an associated role.

 +---------------------+-------------------+-------------------+
 |  'Role'             | Equivalence       | Evidence          |
 +=====================+===================+===================+
 | v'Phantom'          | Trivial/Universal | @()@              |
 +---------------------+-------------------+-------------------+
 | v'Representational' | Representational  | @'Coercible' a b@ |
 +---------------------+-------------------+-------------------+
 | v'Nominal'          | Nominal           | @a ~ b@           |
 +---------------------+-------------------+-------------------+

-}
data Exactly (r :: RoleKind) a b where
  PhantEx ::                  Exactly Phantom          a b
  ReprEx  :: Coercible a b => Exactly Representational a b
  NomEx   ::                  Exactly Nominal          a a

deriving instance Show (Exactly r a b)
deriving instance Eq   (Exactly r a b)
deriving instance Ord  (Exactly r a b)

instance KnownRole r => Category (Exactly r) where
  id  = reflEx
  (.) = flip transEx

-- | The 'Role' to which a piece of evidence 'Exactly' corresponds.
roleEx :: Exactly r a b -> Role r
roleEx = \case
  PhantEx -> Phantom
  ReprEx  -> Representational
  NomEx   -> Nominal

-- | Reflexivity.
reflEx :: forall r a. KnownRole r => Exactly r a a
reflEx = case knownRole @r of
  Phantom          -> PhantEx
  Representational -> ReprEx
  Nominal          -> NomEx

-- | Symmetry.
symEx :: Exactly r a b -> Exactly r b a
symEx = \case
  PhantEx -> PhantEx
  ReprEx  -> ReprEx
  NomEx   -> NomEx

-- | 'Role'-homogeneous transitivity.
transEx :: Exactly r a b -> Exactly r b c -> Exactly r a c
transEx PhantEx PhantEx = PhantEx
transEx ReprEx  ReprEx  = ReprEx
transEx NomEx   NomEx   = NomEx

{- |

'Exactly' is a category graded by the 'Min' monoid on 'RoleKind' with identity:

@
'NomEx' :: 'Exactly' t'Nominal' a a
@

-}
hetTransEx
  :: forall r s a b c
  .  Exactly r a b -> Exactly s b c {- ^ -}
  -> Exactly (Min r s) a c
hetTransEx e1 e2 = case r <|=|> s of
  LTI -> expositRole r (transEx           e1 (weakenEx e2))
  EQI ->                transEx           e1           e2
  GTI -> expositRole s case antiSym s r of
    Refl ->             transEx (weakenEx e1)          e2
 where
  r = roleEx e1
  s = roleEx e2

{- |

@'Exactly' _ a b@ is a monoid graded by the 'Max' monoid on 'RoleKind' with identity:

@
'PhantEx' :: 'Exactly' t'Phantom' a b
@

-}
maxEx
  :: Exactly r a b -> Exactly s a b {- ^ -}
  -> Exactly (Max r s) a b
maxEx e1 e2 = case roleEx e1 <|=|> roleEx e2 of
  LTI -> e2
  EQI -> e2
  GTI -> e1

-- | Weaken evidence for one 'Role' to evidence for a lesser @Role@.
weakenEx
  :: forall r s a b
   . (KnownRole r, r <= s)
  => Exactly s a b -> Exactly r a b
weakenEx e = case knownRole @r of
  Phantom          -> PhantEx
  Representational -> case e of
    ReprEx -> ReprEx
    NomEx  -> ReprEx
  Nominal          -> case e of
    NomEx  -> NomEx

-- | If 'SubNominal' functions and their arguments are equivalent, then so are their respective applications.
applyEx
  :: SubNominal g
  => Exactly r f g -> Exactly r a b {- ^ -}
  -> Exactly r (f a) (g b)
applyEx PhantEx PhantEx = PhantEx
applyEx ReprEx  ReprEx  = ReprEx
applyEx NomEx   NomEx   = NomEx

-- | If applications by @'SuperPhantom' f@ are equivalent, then so are the arguments.
innerEx
  :: SuperPhantom f
  => Exactly r (f a) (f b) {- ^ -}
  -> Exactly r a b
innerEx = \case
  PhantEx -> PhantEx
  ReprEx  -> ReprEx
  NomEx   -> NomEx

-- }}}

