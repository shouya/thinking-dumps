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


#### so what exactly is an algebra

omega algebra is a univeral algebra, while not all algebras are necessary
univeral ones.

so for omega alg, first there is a set `|A|`, now we extend the set with a collection
of operations that act on `|A|`, `a_ω : |A|^ar(ω) -> |A|`.

omega algebra homomorphism is a homomorphism from an alg to another
alg. it consists two parts, the morphism of underlying set and the
morphism of operations. the change of set is easy, which is simply a
function `f : |A| -> |B|`. while it takes a little bit think to
understand how the morphism between operation set works.

we use `~>` to denote morphism. so the morphism will have signature:

    f : (|A|^ar(ω) -> |A|) ~> (|B|^ar(ω) -> |B|)

why does omega keeps unchanged? because we are dealing with the
univeral algebra (omega algebra). Ω is not a specific set but more of
a symbolized representation of a univeral set with all
possibilities. What is really important is the underlying set `|A|`
and `|B|`. which is what should be considered carefully.

#### what is f-alg

f-alg first requires an algebra and then an underlying set of the
algebra.

my example. for a given algebra on set A where there are two operations:

    • : A x A -> A
    @ : A -> A
    1 : A

we have a functor `F : Set -> Set` that transforms the set `A` to another set that
`F(A) :=`

    {(•, (a₁, a₂)) | a₁,a₂ ∈ A} ∪
    {(@, (a₁)) | a₁ ∈ A} ∪
    {(1, ())}

a functor, of course, have to transform functions. if we have function
`h : forall a,b ∈ A, a -> b`, then `F(h)(F(A))` will be:

    {(•, (h(a₁), h(a₂))) | a₁,a₂ ∈ A} ∪
    {(@, (h(a₁))) | a₁ ∈ A} ∪
    {(1, ())}

notice that for function `h : a -> b` we have `F : (a -> b) -> F a -> F b`.

f-alg is just a morphism from the codom category of `F` of `A` to `A`, that is, `F(A) -> A`. which is then clear.

#### ex 2.2.1 check above^2 two defn of homomorphisms are eqv


if we have a Ω-alg,
`h(a_ω(x₁, ..., x_ar(ω))) = b_ω(h(x₁), ..., h(x_ar(ω)))`,

which means `h . a_ω = b_ω . fmap h`, which is the same as the
commutative diagram below:

![f-homo](https://cloud.githubusercontent.com/assets/526598/8545106/2c93af8e-2479-11e5-82b0-d44788af63e5.png)

so it's eqv to f-alg.

#### ex 1. for cat `K` and ftor `F : K -> K` check id and comp of f-alg

    for id := a -> a
      ∀ ω, F(id)(ω, (k₁, ..., k_n))
    = ∀ ω, (ω, (id(k₁), ..., id(k_n)))
    = ∀ ω, (ω, (k₁, ..., k_n))`
    = ∀ ω, id(F(K))

    for f := b -> c, g := a -> b
      ∀ ω, F(f.g)(ω, (k₁, ..., k_n))
    = ∀ ω, (ω, ((f.g)(k₁), ..., (f.g)(k_n)))
    = ∀ ω, (ω, (f(g(k₁)), ..., f(g(k_n))))
    = ∀ ω, F(f)(ω, (g(k₁), ..., g(k_n)))
    = ∀ ω, (F(f).F(g))(ω, (k₁, ..., k_n))


#### ex 2. show if f-alg `(A, a)` is the init in cat f-alg then `a` is iso

given an initial alg struct `a : F(A) -> A`, define a homo function
`h : A -> F(A)`, by initiality(why ?), the following square commutes:


            F(h)
    F(A) -----------> F(F(A))
     |                 |
     | a               | F(a)
     |                 |
     v       h         v
     A -------------> F(A)

here shows that `h . a = id_F(A)`, and by `F(a) . F(h) = id_F(A)`,
we have `F(a . h) = F(id_A) => a . h = id_A`. therefore `a` is iso.


from Lambek’s theorem, initial algebra of an endofunctor, ncatlab.org.


## Natural Transformation

#### What is a nat trans

A nattrans from functor `F : C -> D` to functor `G : C -> D` is
defined as as mapping `η : F -> G` such for all `x,y ∈ C`, the
following square commutes:

            η_x
    F(x) --------> G(x)
     |              |
     |              |
     |F(f)          |G(f)
     |              |
     v      η_y     v
    F(y) --------> G(y)

intuitively, it means `∀ x. η(F(x)) = G(x)` and `η` is homomorphic
(shape preserving).

#### Vertial Composition

![vertical composition](https://cloud.githubusercontent.com/assets/526598/8644700/4c015908-290f-11e5-972b-bafd2df38ad3.png)

![vert comp](https://cloud.githubusercontent.com/assets/526598/8644629/91767438-290e-11e5-9998-b4aacc491efd.png)

commutes.

#### Horizontal composition

![horz comp](https://cloud.githubusercontent.com/assets/526598/8644634/9a14353a-290e-11e5-8a86-32622ee42442.png)

the diagram looks like:

![horz comp](https://cloud.githubusercontent.com/assets/526598/8644637/a3cd7488-290e-11e5-833b-cee32207fe31.png)

it turns out to be the naturality square on `β`:

![horz comp](https://cloud.githubusercontent.com/assets/526598/8644644/abecd05a-290e-11e5-9058-8abd5d5478c3.png)

* ref 1. [catster's video course](https://www.youtube.com/watch?v=XnrqHd39Cl0)
* ref 2. [fnats.pdf by andrzej tarlecki](http://www.mimuw.edu.pl/~tarlecki/teaching/ct/slides/fnats.pdf)

#### Naturally isomorphic

think of cat of functors in `[C;D]`, with nat trans's as arrows. an
iso is called a nat iso. (nat trans)

functor `A : C -> D` is said to be naturally isomorphic to functor
`B : C -> D` iff there exists a natural isomorphism from `A` to `B`.

#### Representable functor

a representable functor is a functor of a special form from an
arbitrary cat into cat of sets. [^2]

a functor `F : C -> Set` is said to be represetable if it is nat isoic
to `Hom(A,-)` for some `A ∈ C`.

a representation of `F` is a pair `(A, Φ)` where `Φ : Hom(A,-) -> F`.

[^2]: https://en.wikipedia.org/wiki/Representable_functor

#### ex 1

i didn't learn about exponential category so i skip this part.

#### ex 2 show there is a such uniq nat trans

so first we want to know what is a preorder, as well as what it is as
a category. according to wikipedia, a preorder set is a set with a
reflexive and transitive binary relation. when defined as cat, the
objects are elements of the set, and hom-sets have one or zero element
(one for objs related, zero otherwise) [^1]

look at the diagram below:

             τ_x
    S(x) -----------> T(x)
     |                 |
     |S(f)             |T(f)
     |                 |
     v       τ_y       v
    S(y) -----------> T(y)


existence:

`τ` exists if and only if `S(C) ≤ T(C)` and it makes the diagram
commutes. therefore `τ` is a nat trans.

uniqueness:

suppose we have another nat trans `υ : S ~≻ T` exists iff
`S(C) ≤ T(C)`. `∀ C ∈ 🐈, τ_C(S(C)) = υ_C(S(C))`. suppose we have a
`D ∈ 🐕. st ∀ C ∈ 🐈. S(C) ≠ D`, there is no saying `S(C) ≤ T(C)` and
both `τ,υ : S ~≻ T` does not exist. so in this case, `S` must be
epimorphic, same for `T`.
We conclude `τ_C · S = υ_C · S => τ_C = υ_C`.

[^1]: https://en.wikipedia.org/wiki/Preorder

#### ex 3. show `I_Set : Set -> Set` is rep'd by any singleton set
