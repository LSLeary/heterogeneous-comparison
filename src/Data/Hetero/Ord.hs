
-- --< Header >-- {{{

{-# LANGUAGE GADTs, QuantifiedConstraints, UndecidableInstances #-}

{- |

Description : Heterogeneous comparison with evidence capture
Copyright   : (c) L. S. Leary, 2025

Heterogeneous comparison with evidence capture.

-}

-- }}}

-- --< Exports >-- {{{

module Data.Hetero.Ord (

  -- * HetOrdering
  HetOrdering(..),
  mapHO, bindHO,

  -- * HetOrd
  HetOrd(..), HetOrd',
  defaultHEq, hcompareVia,

) where

-- }}}

-- --< Imports >-- {{{

-- GHC/base
import GHC.TypeLits (SNat, fromSNat, SSymbol, fromSSymbol, SChar, fromSChar)

-- base
import Type.Reflection (TypeRep, SomeTypeRep(..))
import Data.Kind (Type, Constraint)
import Data.Type.Equality ((:~:)(..), (:~~:)(..))
import Data.Type.Ord (OrderingI(..))
import Data.Type.Coercion (Coercion(..))
import Data.Proxy (Proxy(..))
import Data.Functor.Const (Const(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Sum (Sum(..))
import Data.Functor.Compose (Compose(..))

-- ord-axiomata
import Data.Type.Ord.Axiomata (TotalOrder(..), minTO)
import Data.Type.Ord.Lemmata (minDefl1, minDefl2)

-- heterogeneous-comparison
import Data.Hetero.Role (Role(..), KnownRole(..), expositRole, SuperPhantom)
import Data.Hetero.Evidence.Exactly (Exactly(..))
import Data.Hetero.Evidence.AtLeast (AtLeast(..), maxAL, weakenAL, innerAL)
import Data.Hetero.Eq (HetEq(..))

-- }}}

-- --< HetOrdering >-- {{{

-- | 'Ordering' with captured evidence.
data HetOrdering r a b = HLT | HEQ (AtLeast r a b) | HGT

-- | Map over the contained @t'AtLeast' r a b@.
mapHO
  :: (AtLeast r a b -> AtLeast s c d) {- ^ -}
  -> HetOrdering r a b -> HetOrdering s c d
mapHO f ro = bindHO ro (HEQ . f)

-- | Bind the contained @t'AtLeast' r a b@.
bindHO
  :: HetOrdering r a b {- ^ -}
  -> (AtLeast r a b -> HetOrdering s c d)
  -> HetOrdering s c d
bindHO  HLT     _ = HLT
bindHO (HEQ eq) f = f eq
bindHO  HGT     _ = HGT

-- }}}

-- --< HetOrd >-- {{{

-- | Heterogeneous comparison with evidence capture of type equivalence.
class HetEq f => HetOrd f where
  -- | Compare an @f a@ and an @f b@, opportunistically capturing the strongest
  --   type-equivalence evidence we can given the arguments.
  hcompare :: f a -> f b -> HetOrdering (Strength f) a b

type HetOrd' :: (k -> Type) -> Constraint
type HetOrd' f = (KnownRole (Strength f), HetOrd f)

instance HetOrd Proxy where
  hcompare Proxy Proxy = HEQ PhantAL

instance Ord a => HetOrd (Const a) where
  hcompare (Const x) (Const y) = case compare x y of
    LT -> HLT
    EQ -> HEQ PhantAL
    GT -> HGT

instance HetOrd (Coercion a) where hcompare Coercion Coercion = HEQ ReprAL
instance HetOrd ((:~:)    a) where hcompare Refl     Refl     = HEQ NomAL
instance HetOrd ((:~~:)   a) where hcompare HRefl    HRefl    = HEQ NomAL

instance HetOrd TypeRep where hcompare = hcompareVia SomeTypeRep
instance HetOrd SNat    where hcompare = hcompareVia fromSNat
instance HetOrd SSymbol where hcompare = hcompareVia fromSSymbol
instance HetOrd SChar   where hcompare = hcompareVia fromSChar

instance HetOrd Role where
  hcompare r s = case r <|=|> s of
    LTI -> HLT
    EQI -> HEQ NomAL
    GTI -> HGT

instance HetOrd (Exactly r a) where
  hcompare PhantEx PhantEx = HEQ PhantAL
  hcompare ReprEx  ReprEx  = HEQ ReprAL
  hcompare NomEx   NomEx   = HEQ NomAL

instance HetOrd (AtLeast r a) where
  hcompare PhantAL PhantAL = HEQ PhantAL
  hcompare PhantAL _       = HLT
  hcompare ReprAL  PhantAL = HGT
  hcompare ReprAL  ReprAL  = HEQ ReprAL
  hcompare ReprAL  NomAL   = HLT
  hcompare NomAL   NomAL   = HEQ NomAL
  hcompare NomAL   _       = HGT

instance (HetOrd' f, HetOrd' g) => HetOrd (Product f g) where
  Pair fx gx `hcompare` Pair fy gy = bindHO (fx `hcompare` fy) \eqf ->
    mapHO (maxAL eqf) (gx `hcompare` gy)

instance (HetOrd' f, HetOrd' g) => HetOrd (Sum f g) where
  hcompare = expositRole mfg \case
    InL fx -> \case
      InL fy -> case minDefl1 rf rg of
        Refl -> mapHO weakenAL (fx `hcompare` fy)
      InR _  -> HLT
    InR gx -> \case
      InL _  -> HGT
      InR gy -> case minDefl2 rf rg of
        Refl -> mapHO weakenAL (gx `hcompare` gy)
   where
    rf = knownRole @(Strength f)
    rg = knownRole @(Strength g)
    mfg = minTO rf rg

instance (HetOrd f, SuperPhantom g) => HetOrd (Compose f g) where
  Compose fgx `hcompare` Compose fgy
    = mapHO innerAL (fgx `hcompare` fgy)

-- | A default implementation of 'heq' in terms of 'hcompare'.
defaultHEq :: HetOrd f => f a -> f b -> Maybe (AtLeast (Strength f) a b)
defaultHEq fx fy = case fx `hcompare` fy of
  HEQ eq -> Just eq
  _      -> Nothing

-- | An implementation of 'hcompare' in terms of 'heq' and a strictly increasing /unifier/.
hcompareVia
  :: (HetEq f, Ord y)
  => (forall x. f x -> y) -> f a -> f b {- ^ -}
  -> HetOrdering (Strength f) a b
hcompareVia unify fx fy = case compare (unify fx) (unify fy) of
  LT -> HLT
  EQ -> HEQ case fx `heq` fy of
    Just eq -> eq
    Nothing -> error "hcompareVia: bad unifier."
  GT -> HGT

-- }}}

