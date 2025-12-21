
-- --< Header >-- {{{

{-# LANGUAGE MagicHash, UnboxedTuples #-}

{- |

Description : Unique 'Symbol' Generation
Copyright   : (c) L. S. Leary, 2025

Unique 'Symbol' Generation

-}

-- }}}

-- --< Exports & Imports >-- {{{

module Control.Monad.USG (

  -- * USG
  USG, runUSG,

  -- * Symbol
  Symbol,
  newSymbol,
  newSymbolIO,

  -- * Re-exports
  RealWorld,

) where

-- GHC/base
import GHC.Exts
  ( MutableByteArray#, newByteArray#, fetchAddIntArray#
  , readInt64Array#, writeInt64Array#, casInt64Array#
  , Int(I#), intToInt64#, plusInt64#, eqInt64#, isTrue#
  )
import GHC.Int (Int64(I64#))

-- base
import System.IO.Unsafe (unsafePerformIO)
import Data.Kind (Type)
import Data.Word (Word64)
import Data.Bits (FiniteBits(finiteBitSize))
import Control.Monad (join)
import Control.Monad.ST (ST, runST, RealWorld)

-- primitive
import Data.Primitive.ByteArray (MutableByteArray(..))
import Control.Monad.Primitive (PrimMonad(..))

-- deepseq
import Control.DeepSeq (NFData)

-- hashable
import Data.Hashable (Hashable)

-- }}}

-- --< USG >-- {{{

-- | A pure 'Monad' generating locally unique 'Symbol's.
newtype USG s a = MkUSG{ ($$) :: MutableByteArray# s -> ST s a }
  deriving Functor

instance Applicative (USG s) where
  pure x = MkUSG \_ -> pure x
  liftA2 f ux uy = MkUSG \a -> liftA2 f (ux $$ a) (uy $$ a)

instance Monad (USG s) where
  ux >>= k = MkUSG \a -> do
    x <- ux $$ a
    k x $$ a

-- | Run a fully isolated 'USG' action.
runUSG :: (forall s. USG s a) -> a
runUSG g = runST $ with64b \a ->
  g $$ a

-- }}}

-- --< Symbol >-- {{{

-- | Locally unique 'Symbol's.
type role Symbol    nominal
type      Symbol :: Type -> Type
newtype   Symbol    s    =  MkSymbol Word64 -- pretend |Word64| = ω
  deriving newtype
    ( Eq
    , Ord -- ^ Ordered by time of creation.
    , NFData
    , Hashable
    )

instance Show (Symbol s) where
  showsPrec _ (MkSymbol w)
    = showString "<Symbol:" . showsPrec 0 w . showChar '>'

-- | Create a new 'Symbol' that's unique in the state thread @s@.
newSymbol :: USG s (Symbol s)
newSymbol = MkUSG newSymbolFrom

-- | Create a new 'Symbol' that's unique in the @RealWorld@.
newSymbolIO :: IO (Symbol RealWorld)
newSymbolIO = case global of
  MutableByteArray a -> newSymbolFrom a
 where
  {-# NOINLINE global #-}
  global = (unsafePerformIO . with64b) \a ->
    pure (MutableByteArray a)

newSymbolFrom
  :: PrimMonad m
  => MutableByteArray# (PrimState m) -> m (Symbol (PrimState m))
newSymbolFrom = if finiteBitSize (0 :: Word) == 64
  then fetchAddIncInt
  else casIncInt64
 where
  fetchAddIncInt a = MkSymbol . fromIntegral <$> primitive \s ->
    case fetchAddIntArray# a 0# 1# s of
      (# s', i #) -> (# s', I# i #)
  casIncInt64    a = MkSymbol . fromIntegral <$> primitive \s ->
    case readInt64Array#   a 0#    s of
      (# s', i #) -> case cas i s' of
        (# s'', j #) -> (# s'', I64# j #)
   where
    cas i s = case casInt64Array# a 0# i i' s of
      t@(# s', j #) | isTrue# (eqInt64# i j) -> t
                    | otherwise              -> cas j s'
     where i' = plusInt64# i (intToInt64# 1#)

with64b :: PrimMonad m => (MutableByteArray# (PrimState m) -> m r) -> m r
with64b k = (join . primitive) \s -> case newByteArray# 8# s of
  (# s', a #) -> (# writeInt64Array# a 0# (intToInt64# 0#) s', k a #)

-- }}}

