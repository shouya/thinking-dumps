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
