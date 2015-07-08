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

#### hom-functor

    C(A, -)(B) := C(A,B)
    C(A, f : B -> C)(g : A -> B) := f . g : A -> C, or C(A,C)
    => C(A, f : B -> C) : C(A,B) -> C(A,C)

```haskell
fobj x = [arr, forall arr : a -> x] -- abbr to forall a -> x below
fmap (f :: b -> c) = (forall a -> b) ~> (forall a -> c)
```

the set `C(A,B)` is called a hom-set.

in haskell, this is the `instance Functor (a ->)`.


#### ex 2.1.12 def contravariant version and bifunctor version hom-functors

contravariant: `C(-, B)`: `contramap :: (a -> c) ~> ((c -> b) -> (a -> b))`

```haskell
instance Contravariant (-> b) where
    contramap :: (a -> c) -> (f c -> f a)
    contramap :: (a -> c) -> ((c -> b) -> (a -> b))
    contramap f g = g . f
```

bifunctor `C(-,-)`:

accroding to
[easy](https://www.fpcomplete.com/school/to-infinity-and-beyond/pick-of-the-week/profunctors), A `Profunctor` is [just](http://james-iry.blogspot.jp/2009/05/brief-incomplete-and-mostly-wrong.html) a bifunctor that is contravariant in the first argument and covariant in the second. [What's the problem](http://www.quickmeme.com/meme/3r455v/)?

```haskell
class Profunctor p where
    dimap :: (a -> b) -> (c -> d) -> p b c -> p a d

instance Profunctor (->) where
    dimap :: (a -> b) -> (c -> d) -> (b -> c) -> (a -> d)
    dimap ab cd bc = ab >>> bc >>> cd
```

They are so easy.

## 2.2 *F*-Algebra

#### Ω-algebra

A universal algebra is a three tuple: `(|A|, Ω, a_ω)`

* `|A|` denotes `A` as a set
* `Ω` is a set of operation symbols

For a universal algebra, there is a function called `ar` that
determines the arity of a symbol. `ar : Ω -> ℕ`.

And what is `a_ω`? It is a mapping function `a_ω : |A|^{ar(ω)} → |A|`
for all possible `ω`s. (![omega](https://cloud.githubusercontent.com/assets/526598/8444214/61150658-1f5c-11e5-8558-de849f1094b2.png))

#### Two ways to describe Ω-alg homomorphism

* Ω-alg homomorphism is defined as a function `h : |A| -> |B|` where
   for each `ω ∈ Ω` and `(x₁, x₂, ..., x_{ar(ω)}) ∈ |A|^ar{ω}`,

```
h(a_ω(x₁, x₂, ..., x_{ar(ω)})) = b_ω(h(x₁), h(x₂), ..., h(x_{ar(ω))}
```

* F-homomorphism from `(|A|, a)` to `(|B|, b)` is a function
   `h : |A| -> |B|` such that the following diagram commutes:

![f-homo](https://cloud.githubusercontent.com/assets/526598/8545106/2c93af8e-2479-11e5-82b0-d44788af63e5.png)


#### ex 2.2.1 check above two defn are eqv
