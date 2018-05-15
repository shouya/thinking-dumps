module Syntax


-- Gettin used to idris's syntax and type system
--
-- Those that are same as haskell are omitted, complicated syntax (like with)
-- are played in other files


-- all top-level functions/variables' types must be explicitly declared
foo : String
foo = "hello"

-- String in idris are not List Char, but rather packed Text as in haskell
bar : List Char
bar = unpack foo


-- Nat is unbound integer within [0,inf), inductively defined
data Nat' : Type where
  Z' : Nat'
  S' : Nat' -> Nat'

-- One can either use the GADT style to define a data, or simply:
data Nat'' = Z'' | S'' Nat''

replicate1 : Nat -> List Nat
replicate1 Z = []
-- replicate1 0 = Nil       -- the same
replicate1 (S k) = 1 :: replicate1 k
-- here the value 1's type is automatically set to Nat because it knows it's
-- constructing a list of Nat

-- [] is the syntatic sugar for Nil. [1,2,3] is for 1::2::3::Nil

-- idris allows overloading functions over argument types, as long as there is
-- they are defined in different namespaces,
--
-- the compiler will figure out which definition to use automatically when
-- calling with arguments with different types

-- finite set captures the idea of matching Nat that are less than or equal to a
-- given Nat.
data Fin' : Nat -> Type where
  FZ' : Fin' (S k)
  FS' : Fin' k -> Fin' (S k)


-- typeclass in haskell ~= interfaces in idris, the instance implementation
-- syntax is slightly different:

Show Nat' where
  show Z' = "Z"
  show (S' n) = "S (" ++ show n ++ ")"


-- idris doesn't have things like Constraint at the kind level. Interfaces (or
-- typeclass in haskell) are implemented as partial functions. i.e. unsatisfied
-- types are not implemented.
--
-- example with Show : Type -> Type, where Show Nat : Type is implemented and
-- Show (Nat -> Nat) : Type is not implemented (doesn't have a proof).

-- more sensible Functor/Applicative/Monad interfaces
--
-- Functor has `map' instead of `fmap' as its implementation
--
-- Applicative has `pure' and `<*>', same as Haskell
--
-- Monad has `>>=', `return' is not needed, since we already got `pure'



-- do notation works as in haskell. Monad comprehension as well. Monad
-- comprehension requires (Monad m, Alternative m) (for use of guard).
-- Alternative is the same as in haskell.

-- Multiple implementations for the same type with a interface is allowed.
--
-- e.g. Nat can be a Semigroup in two ways: additive and multiplicative
--
-- This is achieved by named impl, where a name is used when defining


[SemiNatMult] Semigroup Nat where
  (<+>) m n = m * n

[SemiNatAdd] Semigroup Nat where
  (<+>) m n = m + n

-- dependent implementation can be achieved with the 'using' syntax
[MonoidNatMult] Monoid Nat using SemiNatMult where
  neutral = 1
[MonoidNatAdd]  Monoid Nat using SemiNatAdd  where
  neutral = 0

-- !-notation makes writing monadic code easier:
--
--

m_add : Maybe Int -> Maybe Int -> Maybe Int
-- without !-notation
-- m_add x y = do x' <- x
--                y' <- y
--                pure (x + y)
-- with !-notation
m_add x y = pure (!x + !y)

-- ! can be thought of like a prefix function with this type:
--
-- (!) : m a -> a

-- Another convenient syntax is the idiom bracket. idiom bracket makes writing
-- Applicative code cleaner:

m_add' : Maybe Int -> Maybe Int -> Maybe Int
-- without idiom bracket:
-- m_add' x y = pure (+) <*> x <*> y
-- with idiom bracket:
m_add' x y = [| x + y |]



-- idris values are by default strict, Lazy values must be declared explicitly.
--
-- Lazy : Type -> Type

my_if : Bool -> Lazy a -> Lazy a -> a
my_if b x y = if b then x else y

-- when we acquire a value of 'a' where we have a 'Lazy a', it will
-- automatically be evaluated.
--
-- similarly, when we acquire a 'Lazy a' where we have an 'a'-typed expr, the
-- expr will be converted into a unresolved lazy value of type 'Lazy a'

-- function definitions are evaluated in the order they are defined therefore
-- you cannot write plain functions depending on each other directly (you can
-- define recursive function with no problem, though). 'mutual' syntax can be
-- used in this situation, in a 'mutual' block, first the type declarations are
-- added, then the function definitions.

fact' : Nat -> Nat
fact' Z = 1
fact' (S n) = (S n) * fact' n


mutual
  even : Nat -> Bool
  even Z = True
  even (S k) = odd k

  odd : Nat -> Bool
  odd Z = False
  odd (S k) = even k

-- infinte data structure are called co-data types.
--
-- codata-types will gets translated into same as a kind of 'Lazy' data types
namespace StreamCodata
  codata Stream' : Type -> Type where
    (::) : (e : a) -> Stream' a -> Stream' a

-- is the same as

namespace StreamInfData
  data Stream'' : Type -> Type where
    (::) : (e : a) -> Inf (Stream'' a) -> Stream'' a

-- since (::) cannot be defined twice under the same namespace, so here we
-- define them under two namespaces. They can be used without distinguishing
-- explicitly since they differ by the type of the second argument.

-- Inf is mostly the same as Lazy except some nauce differences on their effects
-- on totality.


-- just as a canonical example of typical dependent-type language, there's a
-- built-in Vect data structure is the list parametrized with its length.
-- Defined as below:

data Vect' : (n : Nat) -> a -> Type where
  Nil  : Vect' 0 a
  (::) : a -> Vect' n a -> Vect' (S n) a

-- Tuple syntax (a,b), as both type and value, is a syntatic sugar again.
-- (a, b) as a type is Pair a b; (a, b) as a value is MkPair a b

-- There's another interesting data structure called DPair (Dependent Pair). Defined as:

data DPair' : (a : Type) -> (P : a -> Type) -> Type where
  MkDPair' : {P : a -> Type} -> (x : a) -> P x -> DPair' a P

-- where the second element is a value whose type depends on the value of the
-- first argument. In type theory this type is referred to as `Sigma types'.
--
-- There's, again, a syntatic sugar for DPair: (a:A ** p) stands for MkDPair a p

vec : (n : Nat ** Vect' n Int)
vec = (_ ** [1,2])
-- we can write `_' in place of values which the typechecker can infer
-- automatically.

vec' : DPair Nat (\n => Vect' n Int)
vec' = MkDPair _ [3,4]
-- the same, desugared version.
