data Bool : Set where
  true  : Bool
  false : Bool


not : Bool → Bool
not true = false
not false = true


data ℕ : Set where
  O : ℕ
  S : ℕ → ℕ


_+_ : ℕ → ℕ → ℕ
O   + a = a
S a + b = S (a + b)

_*_ : ℕ → ℕ → ℕ
O   * a = O
S a * b = a + (a * b)

_or_ : Bool → Bool → Bool
true  or _ = true
false or b = b


if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y


infixl 60 _*_
infixl 40 _+_
infixr 20 _or_
infix  5 if_then_else_


infixr 40 _::_
data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A


_∘_ : {A : Set} -> {B : A -> Set} -> {C : (x : A) -> B x -> Set} ->
      (f : {x : A} -> (y : B x) -> C x y) -> (g : (x : A) -> B x) ->
      (x : A) -> C x (g x)
_∘_ f g a = f (g a)


plus-two = S ∘ S

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} -> List A -> List A -> List A
[]      ++ ys = ys
x :: xs ++ ys = x :: (xs ++ ys)


data Vec (A : Set) : ℕ -> Set where
  nil  : Vec A O
  cons : (n : ℕ) -> A -> Vec A n -> Vec A (S n)

head : {A : Set} {n : ℕ} -> Vec A (S n) -> A
head (cons n v vs) = v


vmap : {A B : Set} (n : ℕ) -> (A -> B) -> Vec A n -> Vec B n
vmap .O f nil = nil
vmap .(S n) f (cons n x xs) = cons n (f x) (vmap n f xs)


vmap′ : {A B : Set} (n : ℕ) -> (A -> B) -> Vec A n -> Vec B n
vmap′ O f nil = nil
vmap′ (S n) f (cons .n x xs) = cons n (f x) (vmap n f xs)


data Fin : ℕ -> Set where
  fzero : {n : ℕ} -> Fin (S n)
  fsuc  : {n : ℕ} -> Fin n -> Fin (S n)

_!_ : {n : ℕ}{A : Set} -> Vec A n -> Fin n -> A
nil ! ()
cons n x a ! fzero = x
cons n x a ! fsuc b = a ! b



tabulate : {n : ℕ}{A : Set} -> (Fin n -> A) -> Vec A n
tabulate {O} f = nil
tabulate {S n} f = cons n (f fzero) (tabulate (f ∘ fsuc))


data   False : Set where
record True  : Set where


trivial : True
trivial = _


isTrue : Bool -> Set
isTrue true  = True
isTrue false = False


_<_ : ℕ -> ℕ -> Bool
_   < O   = false
O   < S n = true
S m < S n = m < n

length : {A : Set} -> List A -> ℕ
length [] = O
length (x :: xs) = S (length xs)

lookup : {A : Set}(xs : List A)(n : ℕ) -> isTrue (n < length xs) -> A
lookup (x :: xs) O b = x
lookup (x :: xs) (S n) b = lookup xs n b
lookup [] a ()


data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x


data _≤_ : ℕ -> ℕ -> Set where
  ≤O : {m n : ℕ} -> m == n -> m ≤ n
  ≤I : {m n : ℕ} -> m ≤  n -> m ≤ S n


leq-trans : {l m n : ℕ} -> l ≤ m -> m ≤ n -> l ≤ n
leq-trans (≤O refl) b = b
leq-trans a (≤O refl) = a
leq-trans (≤I a) (≤I b) = ≤I (leq-trans (≤I a) b)
