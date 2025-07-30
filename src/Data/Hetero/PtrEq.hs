
-- --< Header >-- {{{

{-# LANGUAGE MagicHash, DataKinds, QuantifiedConstraints #-}

{- |

Description : Heterogeneous pointer equality
Copyright   : (c) L. S. Leary, 2025

Heterogeneous pointer equality.

The offerings of this module should eventually be incorporated into /base/, /stm/ and /primitive/ by:

 * Generalising the types of pointer equality primitives ([#24994](https://gitlab.haskell.org/ghc/ghc/-/issues/24994))

 * Thereby providing 'Data.Type.Coercion.TestCoercion' instances for the the boxings of those primitive types ([#17076](https://gitlab.haskell.org/ghc/ghc/-/issues/17076))

 * Thereby providing 'Data.Type.Coercion.TestCoercion' instances for derived types

-}

-- }}}

-- --< Exports & Imports >-- {{{

module Data.Hetero.PtrEq (

  -- * Pointer Equality

  -- ** Primitive
  -- $primitive
  Array#, sameArray#,
  MutableArray#, sameMutableArray#,
  SmallArray#, sameSmallArray#,
  SmallMutableArray#, sameSmallMutableArray#,
  MutVar#, sameMutVar#,
  TVar#, sameTVar#,
  MVar#, sameMVar#,
  IOPort#, sameIOPort#,
  PromptTag#, samePromptTag#,

  -- ** Derived
  -- $derived
  Chan, sameChan,
  TBQueue, sameTBQueue,
  TChan, sameTChan,
  TMVar, sameTMVar,
  TQueue, sameTQueue,

) where

-- GHC/base
import GHC.Exts
  ( TYPE, RuntimeRep(BoxedRep), UnliftedType, unsafePtrEquality#, isTrue#
  , Array#, MutableArray#, SmallArray#, SmallMutableArray#
  , MutVar#, TVar#, MVar#, IOPort#, PromptTag#
  )

-- base
import Unsafe.Coerce (unsafeCoerce)
import Data.Type.Coercion (Coercion(..))
import Control.Concurrent.Chan (Chan)

-- stm
import Control.Concurrent.STM (TBQueue, TChan, TMVar, TQueue)

-- }}}

-- --< Pointer Equality: Primitive >-- {{{

{- $primitive

"GHC.Exts" provides pointer equality functions for primitive unlifted types of the form:

> sameFoo# :: Foo# a -> Foo# a -> Int#

When appropriate, we generalise the above to:

> sameFoo# :: Foo# a -> Foo# b -> Maybe (Coercion a b)

\[ \]

-}

unsafeSame
  :: forall {k} (f :: k -> UnliftedType) a b
  .  f a -> f b -> Maybe (Coercion a b)
unsafeSame x y = if isTrue# (unsafePtrEquality# x y)
  then Just (unsafeCoerce (Coercion @a @a))
  else Nothing

sameArray#
  :: forall {l} (a :: TYPE (BoxedRep l)) (b :: TYPE (BoxedRep l))
  .  Array# a -> Array# b {- ^ -}
  -> Maybe (Coercion a b)
sameArray# = unsafeSame

sameMutableArray#
  :: forall {l} s (a :: TYPE (BoxedRep l)) (b :: TYPE (BoxedRep l))
  .  MutableArray# s a -> MutableArray# s b {- ^ -}
  -> Maybe (Coercion a b)
sameMutableArray# = unsafeSame

sameSmallArray#
  :: forall {l} (a :: TYPE (BoxedRep l)) (b :: TYPE (BoxedRep l))
  .  SmallArray# a -> SmallArray# b {- ^ -}
  -> Maybe (Coercion a b)
sameSmallArray# = unsafeSame

sameSmallMutableArray#
  :: forall {l} s (a :: TYPE (BoxedRep l)) (b :: TYPE (BoxedRep l))
  .  SmallMutableArray# s a -> SmallMutableArray# s b {- ^ -}
  -> Maybe (Coercion a b)
sameSmallMutableArray# = unsafeSame

sameMutVar#
  :: forall {l} s (a :: TYPE (BoxedRep l)) (b :: TYPE (BoxedRep l))
  .  MutVar# s a -> MutVar# s b {- ^ -}
  -> Maybe (Coercion a b)
sameMutVar# = unsafeSame

sameTVar#
  :: forall {l} s (a :: TYPE (BoxedRep l)) (b :: TYPE (BoxedRep l))
  .  TVar# s a -> TVar# s b {- ^ -}
  -> Maybe (Coercion a b)
sameTVar# = unsafeSame

sameMVar#
  :: forall {l} s (a :: TYPE (BoxedRep l)) (b :: TYPE (BoxedRep l))
  .  MVar# s a -> MVar# s b {- ^ -}
  -> Maybe (Coercion a b)
sameMVar# = unsafeSame

sameIOPort#
  :: forall {l} s (a :: TYPE (BoxedRep l)) (b :: TYPE (BoxedRep l))
  .  IOPort# s a -> IOPort# s b {- ^ -}
  -> Maybe (Coercion a b)
sameIOPort# = unsafeSame

samePromptTag# :: PromptTag# a -> PromptTag# b -> Maybe (Coercion a b)
samePromptTag# = unsafeSame

-- }}}

-- --< Pointer Equality: Derived >-- {{{

{- $derived

There are various types in /base/ and /stm/ derived from the primitive types above, but for which opacity precludes leveraging the corresponding functions.
Accordingly, we provide additional @sameFoo@ functions for them here.

\[ \]

-}

unsafeSameC
  :: forall f a b
   . (forall x. Eq (f x))
  => f a -> f b -> Maybe (Coercion a b)
unsafeSameC x y = if x == unsafeCoerce y
  then Just (unsafeCoerce (Coercion @a @a))
  else Nothing

sameChan :: Chan a -> Chan b -> Maybe (Coercion a b)
sameChan = unsafeSameC

sameTBQueue :: TBQueue a -> TBQueue b -> Maybe (Coercion a b)
sameTBQueue = unsafeSameC

sameTChan :: TChan a -> TChan b -> Maybe (Coercion a b)
sameTChan = unsafeSameC

sameTMVar :: TMVar a -> TMVar b -> Maybe (Coercion a b)
sameTMVar = unsafeSameC

sameTQueue :: TQueue a -> TQueue b -> Maybe (Coercion a b)
sameTQueue = unsafeSameC

-- }}}

