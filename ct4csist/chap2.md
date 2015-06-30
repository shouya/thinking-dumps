# Chapter 2. Functors, Natural Transformations, and Adjoints

## 2.1 Functors

#### Basic concept

domain/codomain of a morphism are objects in a category.

domain/codomain of a functor are categories.

a functor is a morphism in category of categories.

a functor maps objects to objects and arrows to arrows.

a functor is a homomorphism between two categories.

to preserve the laws in a category, the following must stands:

1. `F(id_A) = id_F(a)`, identity law
2. `F(g . f) = F(g) . F(f)`, compostability law

#### Example of functors

**List**

F : S -> List(S)

	F(A) = [A] : A -> List A
	F(f) = map f : (A -> A') -> (List A -> List A')

* `F(id) = map id xs = xs = id`
* `F(g . f)(xs) = map (f . g) xs = map f (map g xs) = (map f . map g) xs`

**Forgetful functor `U : Mon -> Set`**

Only the set part is preserved.

* obj mapping: `(M, _, _) ~> M`
* arr mapping: `((M, _, _) -> (M', _, _)) ~> (M -> M')`

`fmap f (m, _, _) = f m`


**id functor `I_c`**

* obj mapping: `A ~> A`
* arr mapping: `(A -> B) ~> (A -> B)`

`fmap f x = f x`

**right product with `A` functor**

* obj mapping: `X ~> X x A`
* arr mapping: `(X -> Y) ~> (X x A -> Y x A)`

`fmap f x = (f x, A)`

#### ex 1. construct functors in examples

see above.

#### ex 2. show powerset operator `P` can be a functor `P : Set -> Set`

* obj mapping: `S -> superset of S`, where `S : Set`
* arr mapping: `(S -> S') -> (superset of S -> Superset of S')`

```haskell
-- suppose the set itown is at last
fobj o = subsequences o
fmap f = subsequences . fmap f . last
```

#### ex 3. functor from monoid `M` to monoid `N`

it's just a monoid homomorphism!

#### ex 4. state action of diagonal functor Δ

* obj mapping: `X ~> X ⨯ X`
* arr mapping: `(X -> X') ~> (X ⨯ X -> X' ⨯ X')`

```haskell
fobj x = (x, x)
fmap f (x, _) = (f x, f x)
```
