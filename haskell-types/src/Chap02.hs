{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module Chap02 where

import GHC.TypeLits

{-
Chapter 2 Terms, Types and Kinds
-}


-- Ex 2.1.3-i
-- Q: If Show Int has kind CONSTRAINT, what’s the kind of Show?
-- A: Show :: Type -> Constraint

-- Ex 2.1.3-ii
-- Q: What is the kind of Functor?
-- A: (Type -> Type) -> Constraint

-- Ex 2.1.3-iii
-- Q: What is the kind of Monad?
-- A: (Type -> Type) -> Constraint

-- Ex 2.1.3-iv
-- Q: What is the kind of MonadTrans?
-- A: (Type -> Type) -> Type -> Type -> Constraint
{-
class MonadTrans t where
  lift :: Monad m => m a -> t m a
-}
