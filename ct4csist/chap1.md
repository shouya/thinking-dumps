
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

the product of set `A` and `B` over the **Set** category is `A × B`, the cartesian product set of `A` and `B`. (`{(a,b) | a ∈ A, b ∈ B}`)

whenever you have two a pair of morphisms (total functions) `f` and `g` that maps from a set `V` to `A` and `B`. ee can always construct a total function `h(v) := <f(v), g(v)>` such that maps from `v` to `A × B`. we can prove such factorization is unique.

`π1 : A × B → A` and `π2 : A × B → B` are called the projection functions.


**coproduct**

similarly, the co-product of set `A` and `B` is, `A || B`, the disjoint union of `A` and `B`. (`A × {0} ∪ B × {1}`)

whenever we have `p1 : A -> V` and `p2 : B -> V`, we can construct a total function `h : A || B -> V` by `h(Left(a)) = p1 a; h(Right(b)) = p2 b`. such morphism is unique.


#### uniqueness of prod/coprod up to iso (also ex 1.5.2)

**prod -> iso**

theorem: any two products are iso

proof: suppose we have two products of a set `P` and `P'`. By defn, there exists a uniq factorization from any other same-shape (reversed v-shaped) objects to `P` and also to `P'`. `P` and `P'` are both product so they have the same reversed v-shapes. Therefore there exists uniq `f : P -> P'` and `g : P' -> P` such that `g ∘ f = f ∘ g = id`. Hence `g = f^{-1} and f = g^{-1}`, `P` is iso to `P'`.

**iso -> prod**

theorem: whenever an object is iso to a product, it is also a product.

proof: suppose we have a product `P` of object `A` and `B` and an isomorphic obj `K` to it, we have `f : P -> K` and `f^-1 : K -> P` such that `f . f^-1 = f^-1 . f = id`. We show `K` will also be a product of `A` and `B`.

We can construct the projection arrows `π1 . f^-1 : K -> A` and `π2 . f^-1 : K -> B` therefore `K` would have the same reversed v-shape. By defn, for all `V` with the same shape we have unique factorization `h : V -> P`. We can construct a factorization `f . h : V -> K`, specially, we have factorization from `P`: `f : P -> K`. In this way we proved `K` is a product.

**coprod**:

(偷懶中～～) coprod is the dual of prod. the iso property holds for prod therefore the dual of iso, which is still iso, holds for coprod.


#### ex 1. show `<f . h, g . h> = <f, g> . h`

	  <f . h, g . h> x
	= <(f . h) x, (g . h) x>
	= <f (h x), g (h x)>
	= <f, g> (h x)
	= (<f, g> . h) x

#### ex 2. show `(f × h) . <g, k> = <f . g, h . k>`

	  ((f × h) . <g, k>) a
	= (f x h) <g a, k a>
	= <f (g a), h (k a)>
	= <f . g, h . k> a


#### ex 3. show `(f × h) . (g × k) = <f . h, h . k>`

	  ((f x h) . (g x k) a)
	= (f x h) <g a, k a>
	= <f (g a), h (k a)>
	= <f . g, h . k> a

#### ex 4. prod in A poset cat

<del>as described, on poset `(A, ≤)`, the product of `m` and `n` is `min m n`.</del>

revision: this is not really true because poset does not require `forall x y, x <= y or y <= x`. the answer should be the greatest lower bound of `m` and `n`. Simply consider this post:

![inclusion poset](https://upload.wikimedia.org/wikipedia/commons/thumb/e/ea/Hasse_diagram_of_powerset_of_3.svg/500px-Hasse_diagram_of_powerset_of_3.svg.png)

this is a poset of power set of `{x, y, z}` ordered by inclusion. The product of `{x}` and `{z}` is obviously `{x,z}` rather than any of `{x}` or `{z}`.

#### ex 5. coprod in cat of posetS

category of posets:

* obj: posets, ie. (`{(X, ≤) forall set X}`)
* arr: monotone total functions (total func that preserves `≤`)

this question takes a little bit thinking on it and was interesting. here's how i conceive the answer:
  
![coprod](https://cloud.githubusercontent.com/assets/526598/8224838/17d5084a-155b-11e5-811d-79f850cff1ae.png)

suppose we have a copro `S` of `X` and `Y`, and `p : X -> S, q : Y -> S` are monotone func. Then we conceive two other monotone func `f : X -> V, g : Y -> V` that maps `X` and `Y` to `V`. To say `S` is the copro, we must show there are uniq monotone func from `S` to `V`. How can we choose `p` and `q` to get a `S` such that there exists a uniq morphism `h : S -> V`? simply we do the same as we do for **Set**. We choose `p x = (0, x)` and `q y = (1, y)` so we get `h (0, x) = f x; h (1, y) = g y`. The procedure works with **Set** should also work for **Pos**, but the point is, is `S` we defined here a poset and is `h` a monotone func?

Simply we can't define `S` like that, but we need to find a way to connect two posets with order preserved. I don't know if there is such a way but it should exist and whenever the order is preserved, we can ensure to have `h` as a monotonic function from `S` to `V`.


#### ex 6. find a cat with no prod

the finite category **2**.

#### ex 7. to what does defn 1.5.5 reduce for `|I| = 0`

It is an one-element set. `K^0 = 1` can't it be even more intuitive?

And the coprod/sum of an empty element set is the initial. `0*K = 0`. Isn't it awesome?

### 1.7 equalizers

#### ex 1.7.2 universal construction of equalizer

![universal construction of equalizer](https://cloud.githubusercontent.com/assets/526598/8248738/789989dc-1630-11e5-908d-73b133f19645.png)

#### intuition

as the name suggests, an equalizer maps a range of values to a range of values for which `f` and `g` are defined equal. It could usually be considered as a filter.

#### equalizer on Set of `f` and `g`


	X = {x | x ∈ A, f(x) = g(x)}

the eqzr `e : X -> A` is the inclusion function maps each element `x ∈ X` to the same `x ∈ A`. That is, `e` acts as `id_X` while ignoring some `a ∈ A` for which `f a ≠ g a`.

**Proof**: suppose we have another morphism with the same universal construction, `e' : X' -> A` of `f` and `g`. so we have `f (e' x') = g (e' x')`. We define `k` as follows:

	k : X' -> X
	k x' = e' x'

Because `e' x'` always fall on a range of those 'valid' values of `A`, it was defined to be a subset of `X`. Therefore this mapping `k` exists and satisfy our requirement.

#### ex 1. show only eqzr of cat poset are id arrs

intuitively, let's first find a pair of arrs `f` and `g` from obj `A` to obj `B`. by defn, there is only uniq `f, g : A -> B` that exists. Therefore there is no need to 'filter' the input of `f` and `g` to make them equivalent on this domain, as there are born equal. No filtering, so it is the `id` arrow.

(TODO: prove it)

#### ex 2. show eqzr are monic

monic: left cancel-ability

we are to prove for all `p, q : K -> X`, `e . p = e . q` implies `p = q`.

(ref. http://math.stackexchange.com/q/81296/120022)

we have `f . e = g . e`:

	   (f . e) . p = (g . e) . p
	=> f . (e . p) = g . (e . p)

That is, `e . p` is an universal construction to the equalizer `e`. Therefore we always have a unique morphism `h` from `K` to `X` (mediating arrow by defn of `e`), such that `e . h = e . p`. Since `K -> X` is uniq, we have `h = p = q`. Therefore `e` is monic.

#### ex 3. show epic eqzr are isos

this can be shown by intuition. an eqzr acts like a "filter" to restrict the input of `f` and `g`. when `e` becomes epic, `e . f = e . g => f = g`, the filter is no longer needed and `f` and `g` are always equal. hence passing through the filter no longer lose any info. this is how iso works.

(ref. http://math.stackexchange.com/a/510816/120022)

Proof: We show `id_A` is an equalizer of `f, g : A -> B` for `f = g`. Since `f = g`, `f . id_A = g . id_A`, `id_A` is a general construction. We suppose there exists another general construction `e' : X -> A`. we always have the mediating arrow `e' : X -> A` such that `id_A . e' = id_A . e`. And we know `id_A` is an iso.


## 1.8 Pullbacks

#### general construction of pullbacks

![pullback](https://cloud.githubusercontent.com/assets/526598/8267205/29fb75de-1724-11e5-93e9-86fdea4b1533.png)

pullback is the `P` resulting from `f` and `g`.

such that:

![pullback](https://cloud.githubusercontent.com/assets/526598/8267211/76688628-1724-11e5-85ad-0b3d5ad8f504.png)

it's like a product but:

1. a pullback requires the pair of morphs `f : A -> C, g : B -> C`
2. a pullback is defined on top of morphs `f` and `g` instead of objs `A` and `B`.

#### ex 1 (a) left & right are pullbacks -> outer is pullback

I borrow the diagram from another source.

![pasting of pullbacks](https://cloud.githubusercontent.com/assets/526598/8300231/6430ee0e-1950-11e5-8655-8d3da536fe32.png)

Suppose for a `B` we have `h` and `k`. Here's a brief deduction.

	g . h
    α', ∵ (g . h), k, right square as a pullback
    α'' exists and is uniq, ∵ α', h, left square as a pullback

thus the outer square is a pullback.

#### ex 1 (a) outer is pullback -> left & right are pullbacks

I borrow the diagram from another source.

![pasting of pullbacks](https://cloud.githubusercontent.com/assets/526598/8300231/6430ee0e-1950-11e5-8655-8d3da536fe32.png)

As the outer square is a pullback, we know `α''` exists and is uniq. For any `α'` such that `a' . α' = g . h`, we have `f' . α' = k`, and therefore `α''` is uniq. Then the left square is a pullback.



