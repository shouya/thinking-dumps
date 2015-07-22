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

a nat trans `τ : F -> G` whose components `τ_A` are iso is called nat
iso from `F` to `G`.

functor `A : C -> D` is said to be naturally isomorphic to functor
`B : C -> D` iff there exists a natural isomorphism from `A` to `B`.

#### Representable functor

a representable functor is a functor of a special form from an
arbitrary cat into cat of sets. [^2]

a functor `F : C -> Set` is said to be represetable if it is nat isoic
to `Hom(A,-)` for some `A ∈ C`, we say `F` is representable by `A`.

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


`-> : const` and `<- : point`


          → : λa.x
    I(X) ----------> hom({A},X)
     |    ← : f a     |
     |                |
     v                v
    I(Y) ----------> hom({A},Y)


#### ex 4. show forgetful f'tor `U : Mon -> Set` is rep'd by mon `(ℕ,+,0)`

    U(X) -----------> hom((ℕ,+,0),X)
     |                 |
     |                 |
     v                 v
    U(Y) -----------> hom((ℕ,+,0),Y)

`-> : const` and `<- : xxx`

because there exists monoid homomorphism
`forall M. xxx : (ℕ,+,0) -> (M,•,e)`.

#### ex 5. extend cat FPL with lists and poly funcs on lists

**functors:**

* `List : FPL ~> List FPL`, `λx.[x]` and `fmap`
* `Length : List FPL -> {Int} ⊂ FPL`, `len` and `fmap len`

**nat trans:**

* `∀ A ∈ X. Cons(A,-) : List X -> List X`

etc.

## (The Catsters) Adjunctions

#### intuitions

for a pair of functors `F : C -> D` and `G : D -> C`


            F
    C <------------> D
            G


* isomorphism: `1_C = GF, FG = 1_D`
* equivalence: `1_C ≅ GF, FG ≅ 1_D`
* adjunction: `1_C ~≻ GF, FG ~≻ 1_C`

#### defn of adj (1)

left adjunction of a pair of functors `F : C -> D` and
`G : C -> D`, denoted as `F ⊣ G`, is a pair of nat trans:

    η : 1_C -> GF     (called unit)
    ε : FG -> 1_D     (called counit)


that satisfies:

       Fη          εF
    F -----> FGF ------> F
     \________________/
             1_C


       ηG          Gε
    G -----> GFG ------> G
     \________________/
             1_D


these two identities are called **triangle identities**.


#### defn of adj (2)

left adj of functors `F : C -> D, G : D -> C` is given by a
nat iso `α : Hom_D(F x, y) ≅ Hom_C(x, G y)` for all `x ∈ C, y ∈ D` (bifunctor).

what are the functors that are naturally iso? (for both `x` and `y`)

    C^op ~> Set
    λx. D(F x, y)     (Hom_D(F -, y))

    C^op ~> Set
    λx. C(x, G y)     (Hom_C(-, G y))

    D ~> Set
    λy. D(F x, y)     (Hom_D(F x, -))

    D ~> Set
    λy. C(x, G y)     (Hom_C(x, G -))


what does the nat squre look like for `f : x -> x'`,


                     α_x'
    Hom_D(F x', y) -----------> Hom_C(x', G y)
        |                           |
        |                           |
        | k1                        | k2
        |                           |
        |                           |
        v            α_x            v
    Hom_D(F x, y) ------------> Hom_C(x, G y)


    k1 : (x -> x') -> (F x' -> y) -> (F x -> y) => k1 f g := g (F f)
    k2 : (x -> x') -> (x' -> G y) -> (x -> G y) => k2 f g := g f


#### eqv of defn (1) and (2)

    Hom_D(F x, y) ≅ Hom_C(x, G y)

for (2) we know `Hom_D(F x, y)` is iso to `Hom_C(x, G y)`.

first we let `y = F x`, then lhs is `1_Fx`, and rhs is
`x -> F.G x`, i.e. `F.G`. so `Hom_D(F x, F x) ≅ Hom_C(x, G (F x))`.

so it is a nat trans `1_D ~≻ GF` which is the unit `η`!

We then let `x = G y`. so `Hom_D(F (G y), y) ≅ Hom_C(G y, G y)`,

it turns out to be `FG ~≻ 1_C`, which is the counit `ε`!


#### adj ftors gives rise to monad on C

let `T` to be `GF : C -> C`.

`η : 1 -> T` is the unit in monad.

`μ : T² -> T` (`GεF : GFGF |-> GF`) is the multiplication in monad.

st the following diagram commutes.

        ηT      Tη                       μT
      T---->T^2<----T            T^3 ----------> T^2
       \     |     /              |               |
        \    |μ   /               |               |
         \   |   /                |Tμ             |μ
          \  |  /                 |               |
           v v v                  v      μ        v
             T                   T^2 -----------> T


## 2.3 Adjoint functors

(some defn are from Abstract and Concrete Categries - the Joy of Cats)[^3]

[^3]: http://katmat.math.uni-bremen.de/acc/acc.pdf

#### types of functors

let `F : A -> B` be a functor.

* `F` is called an **embedding** if `F` is injective on morphisms.

* `F` is called **faithful** if for all pairs of `x,y ∈ A`

    F : Hom_A(x,y) -> Hom_B(F(x), F(y))

is injective. (same as embedding, in CWM)

* `F` is called **fulll** if `F` is surjective on morphisms.


#### concrete categeory

A concrete category is a category that looks like a category of “sets
with extra structure”, that is a category of structured sets. [^4]


a concrete cat over `X` is a cat `A` equipped with a forgetful
faithful functor `U : A -> X`. `X` is called the base of `(A,U)`.

we take `X` as `Set` in most times.

[^4]: http://ncatlab.org/nlab/show/concrete+category

#### universal arrow

in a concrete cat `A` over `Sets`.

a univeral arrow over an `Set` is a structured arrow
`u : Set -> |A|` with dom `Set` that has the following universal
property: for each structured arrow `f : Set -> |a'|` there exists a
uniq `A`-morphism `h : |a| -> |a'|` such the triangle commutes:

         u
    Set --> |a|
       \     |
        \f   | h
         \   |
          \  |
           v v
           |a'|


#### adjoint functor

A functor `G : A -> B` is adjoint if for every `b ∈ B` there exists a
`G`-universal arrow with domain `b`.

#### Adjoint functor defined in ct4csist

* a pair of cat: `C` and `D`
* a pair of functors: `F : C -> D` and `G : D -> C`
* a natural trans: `η : I_C ~≻ (G . F)` (unit)

such that the following triangle commutes:

      η_X
    X --> G(F(X))
     \      |
      \     |
      f\    |G(f^#)
        \   |
         \  |
          v v
          G(Y)

#### examples of adj ftors

> Hom_D(F x, y) ≅ Hom_C(x, G y)

`C` and `1`:

* `"C": 1`, `"D": C`
* `F: (1 : 1) ↦ (0 ：C)`, `G: ∀ c ∈ C. c ↦ 1` (`const 1`)
* `η: I_1 ~≻ I_1, ε: (const 0) ~≻ I_C`
* `C(0_C, Y) ≅ 1(1, 1)`

`Π : C x C -> C` and `Δ : C -> C x C`:

* `"C": C`, `"D": <C, C>, or C x C`
* `F: Δ`, `G: Π`
* `η: X ↦ <X,X>`
* `D(<X,X>, <X',X'>) ≅ C(X, (X',X'))`
