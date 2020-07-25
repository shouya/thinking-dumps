{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}

module Chap04 where

{- Chapter 4 Working with Types -}

import Data.Typeable

broken :: (a -> b) -> a -> b
broken f a = apply
  where -- apply :: b -- this type annotation doesn't work because GHC doesn't
        -- know this 'b' is the same as the 'b' in the top level type sig.
        apply = f a

working :: forall a b. (a -> b) -> a -> b
working f a = apply
  where apply :: b
        apply = f a

-- type 'a' doesn't appear in the right of (=>), thus Hindley-Milner's
-- type inference doesn't work, i.e. 'a' will not be correctly inferred.
--
-- If there is no valid call that can make the function figure out which
-- Typeable instance 'a' is, then it's called 'ambiguous'.
--
-- typeName :: forall a. Typeable a => String
-- typeName = show $ typeRep (Proxy @a)


type family AlwaysUnit a where
  AlwaysUnit a = ()

-- Given this denfinition, are all of the following type signatures non-
-- ambiguous?

-- not ambiguous (a is never bound in a call)
foo :: forall a. AlwaysUnit a -> a
foo = undefined

-- not ambigous (a is never bound in a call)
bar :: forall a b. b -> AlwaysUnit a -> b
bar = undefined

-- ambiguous (no instance of 'a' can be inferred)
baz :: forall a. Show a => AlwaysUnit a -> String
baz = undefined
