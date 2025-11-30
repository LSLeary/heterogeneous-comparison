
-- --< Header >-- {{{

{-#
LANGUAGE
  TypeData, DataKinds, TypeFamilies, QuantifiedConstraints, ImpredicativeTypes
#-}

{- |

Description : Singleton t'Data.Hetero.Role.Role's and corresponding constraints
Copyright   : (c) L. S. Leary, 2025

Singleton 'Role's and corresponding constraints.

-}

-- }}}

-- --< Exports >-- {{{

module Data.Hetero.Role (

  -- * Roles
  RoleKind(..), Role(..),
  KnownRole(..), expositRole,

  -- ** Constraints
  IsPhantom,
  IsRepresentational,
  IsNominal,
  SubNominal,
  SuperPhantom,

) where

-- }}}

-- --< Imports >-- {{{

-- GHC/base
import GHC.Exts (withDict)
-- base
import Data.Kind (Constraint)
import Data.Type.Equality (TestEquality(..), (:~:)(..))
import Data.Type.Ord (Compare, OrderingI(..))
import Data.Coerce (Coercible)

-- ord-axiomata,
import Data.Type.Ord.Axiomata
  ( Equivalence(..), TotalOrder(..), BoundedBelow(..), BoundedAbove(..)
  , Proof(..), Sing
  )

-- }}}

-- --< Roles >-- {{{

-- | The kind of [/roles/](https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/roles.html).
type data RoleKind = Phantom | Representational | Nominal

-- | Singleton roles.
data Role (r :: RoleKind) where
  Phantom          :: Role Phantom
  Representational :: Role Representational
  Nominal          :: Role Nominal

type instance Sing RoleKind = Role

type family CmpRole (a :: RoleKind) (b :: RoleKind) :: Ordering where
  CmpRole r       r       = EQ
  CmpRole Phantom _       = LT
  CmpRole Nominal _       = GT
  CmpRole _       Phantom = GT
  CmpRole _       Nominal = LT

type instance Compare @RoleKind a b = CmpRole a b

instance Equivalence RoleKind where
  Phantom          =? Phantom          = Right Refl
  Representational =? Representational = Right Refl
  Nominal          =? Nominal          = Right Refl
  _                =? _                = Left \case{}

  refl _ = QED

  sub Phantom          Phantom          = Refl
  sub Representational Representational = Refl
  sub Nominal          Nominal          = Refl

instance TotalOrder RoleKind where
  (<|=|>) = \case
    Phantom          -> \case
      Phantom          -> EQI
      Representational -> LTI
      Nominal          -> LTI
    Representational -> \case
      Phantom          -> GTI
      Representational -> EQI
      Nominal          -> LTI
    Nominal          -> \case
      Phantom          -> GTI
      Representational -> GTI
      Nominal          -> EQI

  transLeq Phantom          _                t                = least t
  transLeq r                _                Nominal          = greatest r
  transLeq Representational Representational Representational = QED
  transLeq r                s                t                = case r of
    Representational -> case s of -- b
      Nominal -> case t of        -- r
    Nominal          -> case s of -- u
      Nominal -> case t of        -- h

  antiSym = \case
    Phantom          -> \case
      Phantom          -> Refl
      Representational -> Refl
      Nominal          -> Refl
    Representational -> \case
      Phantom          -> Refl
      Representational -> Refl
      Nominal          -> Refl
    Nominal          -> \case
      Phantom          -> Refl
      Representational -> Refl
      Nominal          -> Refl

instance BoundedBelow RoleKind where
  type LowerBound RoleKind = Phantom
  lowerBound = Phantom
  least = \case
    Phantom          -> QED
    Representational -> QED
    Nominal          -> QED

instance BoundedAbove RoleKind where
  type UpperBound RoleKind = Nominal
  upperBound = Nominal
  greatest = \case
    Phantom          -> QED
    Representational -> QED
    Nominal          -> QED

instance TestEquality Role where
  testEquality r s = either (const Nothing) Just (r =? s)

-- | Get the unique value corresponding to a 'RoleKind'.
class    KnownRole r                where knownRole :: Role r
instance KnownRole Phantom          where knownRole = Phantom
instance KnownRole Representational where knownRole = Representational
instance KnownRole Nominal          where knownRole = Nominal

-- | Make a 'Role' known.
expositRole :: Role r -> (KnownRole r => s) -> s
expositRole = withDict

-- }}}

-- --< Roles: Constraints >-- {{{

type IsPhantom :: (k -> l) -> Constraint
type IsPhantom f = forall x y. Coercible (f x) (f y)

type IsRepresentational :: (k -> l) -> Constraint
type IsRepresentational f = (SubNominal f, SuperPhantom f)

type IsNominal :: (k -> l) -> Constraint
type IsNominal f = forall x y. Coercible (f x) (f y) => x ~ y

type SuperPhantom :: (k -> l) -> Constraint
type SuperPhantom f = forall x y. Coercible (f x) (f y) => Coercible x y

type SubNominal :: (k -> l) -> Constraint
type SubNominal f = forall x y. Coercible x y => Coercible (f x) (f y)

-- }}}

