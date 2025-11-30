
-- --< Header >-- {{{

{-#
LANGUAGE
  DataKinds, TypeFamilies, UndecidableInstances, MagicHash,
  QuantifiedConstraints
#-}

{- |

Description : Heterogeneous equality with evidence capture
Copyright   : (c) L. S. Leary, 2025

Heterogeneous equality with evidence capture.

-}

-- }}}

-- --< Exports >-- {{{

module Data.Hetero.Eq (

  -- * HetEq
  HetEq(..),
  HetEq',

  -- * Newtypes for @DerivingVia@
  TestCo(..),
  TestEq(..),

) where

-- }}}

-- --< Imports >-- {{{

-- GHC/base
import GHC.TypeLits (SNat, SSymbol, SChar)
import GHC.STRef (STRef(..))
import GHC.IORef (IORef(..))
import GHC.MVar (MVar(..))
import GHC.Conc (TVar(..))

-- base
import Type.Reflection (TypeRep)
import Data.Kind (Type, Constraint)
import Data.Type.Equality (TestEquality(..), (:~:)(..), (:~~:)(..))
import Data.Type.Ord (Min, Max)
import Data.Type.Coercion (TestCoercion(..), Coercion(..))
import Data.Proxy (Proxy(..))
import Data.Functor ((<&>), ($>))
import Data.Functor.Const (Const(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Sum (Sum(..))
import Data.Functor.Compose (Compose(..))
import Control.Monad (guard)

-- primitive
import Data.Primitive
  ( Array(..), MutableArray(..), SmallArray(..), SmallMutableArray(..)
  , MutVar(..)
  )
import Data.Primitive.MVar qualified as Prim

-- ord-axiomata
import Data.Type.Ord.Axiomata (minTO, Proof(..))
import Data.Type.Ord.Lemmata (minDefl1, minDefl2)

-- heterogeneous-comparison
import Data.Hetero.PtrEq
import Data.Hetero.Role
  (RoleKind(..), Role(..), KnownRole(..), expositRole, SuperPhantom)
import Data.Hetero.Evidence.Exactly (Exactly(..))
import Data.Hetero.Evidence.AtLeast (AtLeast(..), maxAL, weakenAL, innerAL)

-- }}}

-- --< HetEq >-- {{{

-- | Heterogeneous equality with evidence capture of type equivalence.
class HetEq f where

  -- | Does not correspond precisely to the role signature of @f@ according to GHC, but rather a lower bound on the @Strength@ of the evidence gleaned from a positive equality test.
  type Strength f :: RoleKind

  -- | Compare an @f a@ and an @f b@ for equality, opportunistically capturing the strongest type-equivalence evidence we can given the arguments.
  heq :: f a -> f b -> Maybe (AtLeast (Strength f) a b)

type HetEq' :: (k -> Type) -> Constraint
type HetEq' f = (KnownRole (Strength f), HetEq f)

-- }}}

-- --< HetEq: Phantom >-- {{{

instance HetEq Proxy where
  type Strength Proxy = Phantom
  heq Proxy Proxy = Just PhantAL

instance Eq a => HetEq (Const a) where
  type Strength (Const a) = Phantom
  heq (Const x) (Const y) = guard (x == y) $> PhantAL

-- }}}

-- --< HetEq: Representational >-- {{{

-- | Derives a 'HetEq' instance from 'TestCoercion'.
newtype TestCo f a = TestCo (f a)

instance TestCoercion f => HetEq (TestCo f) where
  type Strength (TestCo f) = Representational
  heq (TestCo fx) (TestCo fy) = testCoercion fx fy <&> \Coercion -> ReprAL

deriving via TestCo (Coercion a) instance HetEq (Coercion a)

instance HetEq (STRef s) where
  type Strength (STRef s) = Representational
  STRef mv1 `heq` STRef mv2 = sameMutVar# mv1 mv2 <&> \Coercion -> ReprAL

instance HetEq IORef where
  type Strength IORef = Representational
  IORef r1 `heq` IORef r2 = r1 `heq` r2

instance HetEq MVar where
  type Strength MVar = Representational
  MVar mv1 `heq` MVar mv2 = sameMVar# mv1 mv2 <&> \Coercion -> ReprAL

instance HetEq TVar where
  type Strength TVar = Representational
  TVar mv1 `heq` TVar mv2 = sameTVar# mv1 mv2 <&> \Coercion -> ReprAL

instance HetEq Chan where
  type Strength Chan = Representational
  c1 `heq` c2 = sameChan c1 c2 <&> \Coercion -> ReprAL

instance HetEq TBQueue where
  type Strength TBQueue = Representational
  c1 `heq` c2 = sameTBQueue c1 c2 <&> \Coercion -> ReprAL

instance HetEq TChan where
  type Strength TChan = Representational
  c1 `heq` c2 = sameTChan c1 c2 <&> \Coercion -> ReprAL

instance HetEq TMVar where
  type Strength TMVar = Representational
  c1 `heq` c2 = sameTMVar c1 c2 <&> \Coercion -> ReprAL

instance HetEq TQueue where
  type Strength TQueue = Representational
  c1 `heq` c2 = sameTQueue c1 c2 <&> \Coercion -> ReprAL

instance HetEq Array where
  type Strength Array = Representational
  Array xs `heq` Array ys = sameArray# xs ys <&> \Coercion -> ReprAL

instance HetEq (MutableArray s) where
  type Strength (MutableArray s) = Representational
  MutableArray xs `heq` MutableArray ys
    = sameMutableArray# xs ys <&> \Coercion -> ReprAL

instance HetEq SmallArray where
  type Strength SmallArray = Representational
  SmallArray xs `heq` SmallArray ys
    = sameSmallArray# xs ys <&> \Coercion -> ReprAL

instance HetEq (SmallMutableArray s) where
  type Strength (SmallMutableArray s) = Representational
  SmallMutableArray xs `heq` SmallMutableArray ys
    = sameSmallMutableArray# xs ys <&> \Coercion -> ReprAL

instance HetEq (MutVar s) where
  type Strength (MutVar s) = Representational
  MutVar mv1 `heq` MutVar mv2 = sameMutVar# mv1 mv2 <&> \Coercion -> ReprAL

instance HetEq (Prim.MVar s) where
  type Strength (Prim.MVar s) = Representational
  Prim.MVar mv1 `heq` Prim.MVar mv2
    = sameMVar# mv1 mv2 <&> \Coercion -> ReprAL

-- primitive instances elided due to lack of opacity:
--
-- instance HetEq PrimArray
-- instance HetEq (MutablePrimArray s)
-- instance HetEq (PrimVar s)

-- }}}

-- --< HetEq: Nominal >-- {{{

-- | Derives a 'HetEq' instance from 'TestEquality'.
newtype TestEq f a = TestEq (f a)

instance TestEquality f => HetEq (TestEq f) where
  type Strength (TestEq f) = Nominal
  heq (TestEq fx) (TestEq fy) = testEquality fx fy <&> \Refl -> NomAL

deriving via TestEq ((:~:)  a) instance HetEq ((:~:)  a)
deriving via TestEq ((:~~:) a) instance HetEq ((:~~:) a)
deriving via TestEq  TypeRep   instance HetEq  TypeRep
deriving via TestEq  SNat      instance HetEq  SNat
deriving via TestEq  SSymbol   instance HetEq  SSymbol
deriving via TestEq  SChar     instance HetEq  SChar
deriving via TestEq  Role      instance HetEq  Role

-- }}}

-- --< HetEq: Dependent >-- {{{

instance HetEq (Exactly r a) where
  type Strength (Exactly r a) = r
  heq PhantEx PhantEx = Just PhantAL
  heq ReprEx  ReprEx  = Just ReprAL
  heq NomEx   NomEx   = Just NomAL

instance HetEq (AtLeast r a) where
  type Strength (AtLeast r a) = r
  heq PhantAL PhantAL = Just PhantAL
  heq ReprAL  ReprAL  = Just ReprAL
  heq NomAL   NomAL   = Just NomAL
  heq _       _       = Nothing

instance (HetEq' f, HetEq' g) => HetEq (Product f g) where
  type Strength (Product f g) = Max (Strength f) (Strength g)
  Pair fx gx `heq` Pair fy gy = liftA2 maxAL (fx `heq` fy) (gx `heq` gy)

instance (HetEq' f, HetEq' g) => HetEq (Sum f g) where
  type Strength (Sum f g) = Min (Strength f) (Strength g)
  sfg1 `heq` sfg2 = expositRole mfg case (sfg1, sfg2) of
    (InL fx, InL fy) -> case minDefl1 rf rg of
      QED -> weakenAL <$> fx `heq` fy
    (InR gx, InR gy) -> case minDefl2 rf rg of
      QED -> weakenAL <$> gx `heq` gy
    _                -> Nothing
   where
    rf = knownRole @(Strength f)
    rg = knownRole @(Strength g)
    mfg = minTO rf rg

instance (HetEq f, SuperPhantom g) => HetEq (Compose f g) where
  type Strength (Compose f g) = Strength f
  Compose fgx `heq` Compose fgy = fgx `heq` fgy <&> innerAL

-- }}}

