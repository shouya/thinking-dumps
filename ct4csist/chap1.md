
## 1.1 Categories

Exercises:

#### 1. show how arbitrary set can be considered as a categroy

Obj(S) := all elements in S

By axiom of choice, we can pick an arbitrary element from S and assign
morphisms from it to other elements. The repeat the same process for
the rest of the elements until there is no element left. After all we
assign identity morphisms for each elements. It's obvious
to see that these morphisms follow the composition law.

The shape is like finite cateogry.


#### 2. show arbitrary group can be considered a category

Obj(C) := {X}
Arr(C) := elements in G, mapping from X to X

id arrow: the identity element in G

It's not difficult to show that: `a . (b . c) = (a . b) . c` by the
definition of the assoc law of the operator `(+)` of group.

#### 3. shape of 3, 4, 5-category and their corresp to nat numbers

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

3+2+1 morphims.

**5-cat:**

too complex to draw in ascii art. just omitted.

there will be 4+3+2+1 morphisms.

#### 4. complete the following spec of cat M.

* Obj(M) := Nat numbers
* M-arrow `f : m -> n` is an m-by-n matrix of real nums
* the composite `g . f` of `f : m -> n` and `g : n -> p` is the matrix prod of `f` and `g`.

the assoc law is implied by the associativity of the product of two
matrix.

the identity arrow on an object n is a n-by-n identity matrix.

#### 5. redraw arrows in FPL category

ommited.

## 1.3 mono-, epi-, and iso-morphisms

So the essential on mono and epi are cancelabilities.

* Mono <=> left  cancellation: `f . g = f . h   ==>   g = h`
* Epi  <=> right cancellation: `g . f = h . f   ==>   g = h`

When it applies to **Set**, we could imagine:

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
