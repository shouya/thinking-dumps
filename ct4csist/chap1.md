
## 1.1 Categories


#### ex 1. show how arbitrary set can be considered as a category

* Obj(S) := all elements in S

By axiom of choice, we can pick an arbitrary element from S and assign
morphisms from it to other elements. The repeat the same process for
the rest of the elements until there is no element left. After all we
assign identity morphisms for each elements. It's obvious
to see that these morphisms follow the composition law.

The shape is like finite category.


#### ex 2. show arbitrary group can be considered a category

* Obj(C) := {X}
* Arr(C) := elements in G, mapping from X to X

id arrow: the identity element in G

It's not difficult to show that: `a . (b . c) = (a . b) . c` by the
definition of the assoc law of the operator `(+)` of group.

#### ex 3. shape of 3, 4, 5-category and their corresp to nat numbers

**3-cat:**

    a-->b
     \  |
      \ |
       vv
        c

2+1 morphisms.

**4-cat:**

    a---->b
    |\   /|
    | \ / |
    |  X  |
    | / \ |
    vv   vv
    c---->d

3+2+1 morphisms.

**5-cat:**

too complex to draw in ascii art. just omitted.

there will be 4+3+2+1 morphisms.

#### ex 4. complete the following spec of cat M.

* Obj(M) := Nat numbers
* M-arrow `f : m -> n` is an m-by-n matrix of real nums
* the composite `g . f` of `f : m -> n` and `g : n -> p` is the matrix prod of `f` and `g`.

the assoc law is implied by the associativity of the product of two
matrix.

the identity arrow on an object n is a n-by-n identity matrix.

#### ex 5. redraw arrows in FPL category

omitted.

## 1.3 mono-, epi-, and iso-morphisms

#### essential of mono and epi

So the essential on mono and epi are cancel-abilities.

* Mono <=> left  cancellation: `f . g = f . h   ==>   g = h`
* Epi  <=> right cancellation: `g . f = h . f   ==>   g = h`

When it applies to **Set**, specially for **R**s, we could imagine:

* mono: if we have `ln(g(x)) = ln(h(x))` and because `ln` never maps
  two distinct values to a same value (i.e. surjective), we could
  conclude that `g(x) = h(x)`

* non-mono: if we have `g(x)^x = h(x)^2`, because `(^2)` is not
  surjective, we cannot come out at `g = h`.

* epi: if we have `g(ln(x)) = h(ln(x))`, because `ln` is onto, that
  means `forall y \in R` there is a `x` such that `ln(x) = y`, which
  means for the complete domain of `g` and `h` they are all mapping to
  the same results. therefore we conclude that `g = h`.

* non-epi: if we have `g(x^2) = h(x^2)`, because `^2` is not onto,
  as for negative reals we can't say that `g(x)` will be still equal
  to `h(x)`. and therefore we cannot come at `g = h`.

#### about iso

the intuition of isomorphism is a `f` between two objs `A` and `B` is
that `A` and `B` has equivalent SHAPE. It means we can transform from
`A` to `B` and `B` to `A` back and forth, without losing any info.

#### ex 1. prove epic <=> onto

**epic -> onto**

by contradiction, assume we have `f : A -> B` which is not onto. there
exists `b0` such that `forall a, f a /= b0`. then suppose there is `g, h : B -> C`.

we can define a `g /= h` by the following spec:

* `g(b) := b` (forall `b`)
* `h(b) := if b == b0 then x0 else b`

with this defn, `g . f === h . f` but `g /== h` because `g(b0) /= h(b0)`.


**onto -> epic**

suppose we have an onto function, `f : A -> B`. then we have `forall
b, exists a, f a = b`. if also we have `g, h : B -> A` and
`g . f = h . f`, which becomes `forall a. g(f(a)) = h(f(a))`.
then we can conclude `forall b, g b = h b` and therefore `g = h`.

#### ex 2. transitivity of monic

`f : A -> B and g : B -> C` are monic, we want to prove
`g . f : A -> C` is also monic. Suppose `h, h' : K -> A`,

        (g .  f) . h  == (g .  f) . h'
     =>  g . (f  . h) ==  g . (f  . h') (assoc of .)
     =>  g .       h  ==  g .       h' (since f is monic)
     =>            h  ==            h' (since g is monic)


#### ex 3. trans of epic

`f : A -> B and g : B -> C` are epic, we want to prove
`g . f : A -> C` is also epic. Suppose `h, h' : C -> K`

         h . (g  . f) ==  h' . (g  . f)
     => (h .  g) . f  == (h' .  g) . f (assoc of .)
     =>  h       . f  ==  h' .       f (since g is epic)
     =>  h            ==  h'           (since f is epic)

#### ex 4. show `f^{-1}` is uniq

we prove by contradiction. suppose `f : A -> B` is iso and there are two
`f^{-1}` : `h0, h1 : B -> A` such that `h0 /= h1`.

Since `h0, h1` are inverse of `f`, we have

        h1 . f  . h0
    => (h1 . f) . h0
    =>  id      . h0
    =>            h0


       h1 .  f . h0
    => h1 . (f . h0)
    => h1 . id
    => h1

Therefore:

    h1 . f . h0 = h0 = h1

which contradicts the assumption `h0 /= h1`. therefore `f^{-1}`
cannot be two distinct functions.


#### ex 5. show f^-1 . g^-1 is the inverse of g . f

* `f : A -> B, f^-1 : B -> A`
* `g : B -> C. g^-1 : C -> B`

           (g .  f) . (f^-1  . g^-1)
        =>  g . (f  .  f^-1) . g^-1
        =>  g . id           . g^-1
        =>  g . g^-1
        =>  id

In similar way we can deduce that `(f^-1 . g^-1) . (g . f)` is
`id`. Therefore `(f^-1 . g^-1)` is the inverse of `(g . f)`.


#### ex 6. find an arrow that is epic and monic but not iso

We adopt the arrow `f` for **2** category. **2** is defined as below:

* Obj(**2**): {A, B}
* Arr(**2**):
  - `f : A -> B`
  - two ids: `id_A, id_B`

`f` is epic because `h0 . f = h1 . f => h0 = h1` because there is only
one morphism satisfy positions of `h0` and `h1`: `id_B`. Similarly
`f` is monic.

But we don't have an inverse of `f` that `f^{-1} : B -> A`. Therefore
`f` is not iso.


## 1.4 initial and terminal obj

#### why 1-elem sets and empty set

First we to know what is meant by the category **Set**. It consists of objects of ALL sets, and the arrows are *total functions*. Total function is defined by:

> if we have a mapping `f : A -> B` such that `forall a : A, exists b : B, such that f a = b`, then we say `f` is a total function.

**Terminals**

So we have an arrow, a total function, from set `A` to set `B`. Now we think of what if we have only one element in `B`. How many ways are there you can define this arrow `f`?

Surely there is only one, the constant function: `f _ = b0`. In this way we define this object as a terminal.

**Initials**

What about initials? The same. Notice that we are having total functions as the morphisms, for `f : A -> B`, if we have `A` a set with 1-elements, we would have a number of `|B|` ways to define `f`. If the number of elements gets more in `A`, the situation become worse, as we would have `|B|^|A|` ways to define such morphisms. If we want the number of morphisms from `A` to any `B` to be exactly one, `|A|` must be zero, and therefore `A` must be `∅`.

This mapping is called a [empty function](https://en.wikipedia.org/wiki/Empty_function). The way it is defined and valid, according to wikipedia, is to maintain the consistency of **Set** as a category such every objects in **Set** can have an identity morphism. The empty function is also defined valid in terms of cardinal arithmetic described above.


#### intuition about init and term obj

so a terminal is denoded as **1**.

and an initial is denoted as **0**.

indicated by the cardinality of the object.

For poset `(A, <=)`, init is the greatest elem and term is the least elem.

#### why there exists unique term obj (up to iso)?

suppose we have any two term obj: `T` and `T'`. By defn, we have one and only one morph from `T` to `T'` since `T'` is a term. Similarly, we also have one and only one morph from `T'` to `T`. Therefore for ally `T` and `T'`, as far as they are both terminals, they must be isomorphic to each other.

#### ex 1. prove terminals are uniq up to iso

already proved above. omitted.

#### ex 2. terms/coterms in **Set x Set**, **Set^{->}**, and a poset

**Set x Set**:

* obj: `{(a,b)|a ∈ Obj(A), b ∈ Obj(B)}`
* arr: `{(f,g)|f ∈ Arr(A), b ∈ Arr(B)}`
* term: one elem sets, ie. `{(a,b)|a ∈ Obj(A), b ∈ Obj(B), |A| = 1 ∧ |B| = 1}`
* coterm: `∅`, because `{(∅ x a) | a ∈ Obj(A)}` = `∅`, same for right product.


**Set^{->}**:

* obj: total functions (arr in `Set`)
* arr: total function homomorphisms (ie. preserve commutativity)
* term: all total functions mapping from `A` to `B` where `|A| = |B| = 1`
* coterm: `id_∅ : ∅ → ∅`


**Poset (A, <=)**:

* obj: elems in `A`
* arr: `(a, b)` (`a -> b`) for all `a <= b`
* term: greatest obj
* coterm: least obj

#### ex 3. find cat with no init/term/both

**No init:**

poset: `({x | x ∈ ℤ ∩ (-∞, 0], <=)`

**No term:**

poset: `({x | x ∈ ℤ ∩ [0, ∞), <=)`

**No both:**

poset: `(ℤ, ≤)`

**Example  1 from the catsters**:

* `Obj(𝒞) = {A,B}`
* `Arr(𝒞) = {f : A → B, g : A → B}`

**Example 2 from the catsters**:

* `Obj(𝒞) = {A,B,C,D}`
* `Arr(𝒞) = {f : A → B, g : C → D}`

**Example 3 from the catsters**:

* `Obj(𝒞) = {A,B,C,D,...}`
* `Arr(𝒞) = {f1 : A -> B, f2 : B -> C, f3 : C -> D, ...}`

This example does not have a terminal, similar to the `(ℤ^+)` poset I described above.


## 1.5 Product

#### clarified defn

a product is an object. it is not really necessary to rely on a category with cartesian products.

#### product on a poset

here is an example of product on poset `({1,2,3,4,5}, ≤)`:

![prod](https://cloud.githubusercontent.com/assets/526598/8203225/50875e02-14ae-11e5-8088-fbc9ebdf61ff.png)

(other arrows are omitted)

From the diagram, we might say the product of `4` and `5` to be `3`. But actually this is not true. If we consider the identity arrow:

![prod](https://cloud.githubusercontent.com/assets/526598/8203237/5b417da0-14ae-11e5-8fb1-493c07683c8f.png)

We can find that actually the object that satisfy the property is `4`!

For category we could have a table:

Object 1 | Object 2 | Product element
---------|----------|----------------
5 | 5 | 5
4 | 5 | 4
3 | 5 | 3
3 | 3 | 3

"The greatest lower bound"


#### prod/coprod on Set

**product**

the product of set `A` and `B` over the **Set** category is `A × B`, the cartesian product set of `A` and `B`. (`{(a,b) | a ∈ A, b ∈ B}`)

whenever you have two a pair of morphisms (total functions) `f` and `g` that maps from a set `V` to `A` and `B`. ee can always construct a total function `h(v) := <f(v), g(v)>` such that maps from `v` to `A × B`. we can prove such factorization is unique.

`π1 : A × B → A` and `π2 : A × B → B` are called the projection functions.


**coproduct**

similarly, the co-product of set `A` and `B` is, `A || B`, the disjoint union of `A` and `B`. (`A × {0} ∪ B × {1}`)

whenever we have `p1 : A -> V` and `p2 : B -> V`, we can construct a total function `h : A || B -> V` by `h(Left(a)) = p1 a; h(Right(b)) = p2 b`. such morphism is unique.


#### uniqueness of prod/coprod up to iso (also ex 1.5.2)

**prod -> iso**

theorem: any two products are iso

proof: suppose we have two products of a set `P` and `P'`. By defn, there exists an uniq factorization from any other same-shape (reversed v-shaped) objects to `P` and also to `P'`. `P` and `P'` are both product so they have the same reversed v-shapes. Therefore there exists uniq `f : P -> P'` and `g : P' -> P` such that `g ∘ f = f ∘ g = id`. Hence `g = f^{-1} and f = g^{-1}`, `P` is iso to `P'`.

**iso -> prod**

theorem: whenever an object is iso to a product, it is also a product.

proof: suppose we have a product `P` of object `A` and `B` and an isomorphic obj `K` to it, we have `f : P -> K` and `f^-1 : K -> P` such that `f . f^-1 = f^-1 . f = id`. We show `K` will also be a product of `A` and `B`.

We can construct the projection arrows `π1 . f^-1 : K -> A` and `π2 . f^-1 : K -> B` therefore `K` would have the same reversed v-shape. By defn, for all `V` with the same shape we have unique factorization `h : V -> P`. We can construct a factorization `f . h : V -> K`, specially, we have factorization from `P`: `f : P -> K`. In this way we proved `K` is a product.


