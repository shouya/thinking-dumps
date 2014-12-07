## Lazy

Lazy evaluation principle in practice

### Why

As I read Heinrich Apfelmus's article
'[How lazy evaluation works in Haskell](https://hackhands.com/lazy-evaluation-works-haskell/)',
I found the mechanism behind Haskell's non-strict lazy evaluation
pretty beautiful. The guide shows me a clear way implementing lazy
evaluation.

I dedicated to translate this article into Chinese, and published [here](http://shouya.github.io/blog/how-lazy-evaluation-works-in-haskell/)
after permission granted from the author.

It was really refreshing to think inside the how different evaluation
models work. So I decided to write a demonstration, also as a trial, on
implementing the different evaluation strategies.

This project will be written in Racket. First, to implement
a experimental language for syntax-independent purpose, a simple Lisp
dialect with s-expression syntax should be the easiest choice. Second,
Racket is one of the my most familiar languages. Finally, unlike Scheme,
Racket has sufficient handy libraries built-in, which would be less
distracting for me to focus on the implementation itself.


### Planned roadmap

* [X] eager evaluation (`eager.rkt`)
* [X] delayed evaluation on arguments (`delay.rkt`)
* [X] delayed evaluation with graph reduction (`delay2.rkt`)
* [X] lazy evaluation with constructor type, capable for recursive
      values and functions (`lazy.rkt`)


Each of these files should be a complete interpreter of a customized minimal
lisp dialect which is ready to be tested.

The testing examples are appended (and commented out) at the end of each files.

Have fun being more and more **lazy**!

## Loli
As I field to implement something using the lazy evalution theory, a
new language was created. It was beautiful and elegant, and most
important, it's adorable. I call she `loli`, as suggested by
[@codeotakuchiyan](https://twitter.com/codeotakuchiyan).

![Loli's - Moegirl Wiki](http://static.mengniang.org/common/c/c1/Roukyubu.jpg)

Loli is a lisp dialect for research purpose, she so far implements
[lazy evaluation](http://en.wikipedia.org/wiki/Lazy_evaluation) and
[algebraic data types](http://en.wikipedia.org/wiki/Algebraic_data_type),
other features are not planned yet.


TL;DR: Read the source of Loli in `lazy.rkt` and the sample Loli programs at the
bottom of the source file. Execute the source in drracket or using
racket CLI to see the result.

### Data types
There are two built-in data types:

* integer (i)
* lambda (λ)
* reference, aka. symbol (r)

And there are other internal data types, which are not accessible
directly by the users:

* application (appl)
* raw lambda, ie. lambda without lexical binding, (λraw)
* closure, ie. an expression with binding, (c)
* typed value, ie. a value constructed by a type construtor, (V)
* procedure, ie. built-in functions, (p)

### Syntax & Details

The syntax of loli is basically s-expression, expressed as a quoted
list in Racket.


#### lambda definition

You may define a lambda that perform a simplest plus operation like this:

```racket
(λ (a b) (+ a b))
```

for one argument lambda, the parentheses are optional, ie. you can write
code like this:

```racket
(λ a (+ 1 a))
```

Loli lambdas always curry, which is to say,

```racket
(λ (a b) (+ a b))
```

is just a syntatic sugar to write

```racket
(λ (a) (λ (b) (+ a b)))
```


Because of purity from lambda calculus, zero argument lambda is not
supported.


*compiler details:* all syntatic sugars, including multi-argument
 lambda and multiple application, are expanded in the compiling
 phase. a lambda definition will be expanded to a `λraw` typed
 expression, which will become a real `λ` when it is being evaluated.


#### application

You can apply values to procedures, as well as to lambdas,

```racket
(+ 1 1)
((λ (a b) (+ a b)) 1 2)
```

Because Loli uses curry functions, applying multiple values is also
just a syntatic sugar.

```racket
(+ 1 1)
```

is equivalent to

```racket
((+ 1) 1)
```



#### algebraic data type definition

For example, if you want to describe a list, you may use the
following ADT definition in Haskell:

```haskell
data List a = Nil
            | Cons a (List a)
```

Notice that when you use type constructors like `Cons`,
it behaves just like a function. It takes curried arguments, and
results in a value with type `List`.

In Loli, constructors (with parameters) *are* just lambdas, also they
yield a value in the defined type. We would call such values as
'typed-values' (V).


In Loli, types are dynamic. So you don't need to specify a type variable
when you are defining an ADT.

Besides, because of the functionality, Loli does not provide a mutable
environment, so you can't `define` a value, or a type, but you can
rather `let` them in a scope.

So let me `let` a simpliest `List` type in Loli:

```racket
(T List ((Cons car cdr)
         (Nil))
  <expression>)
```

`Nil` requires no argument, so it refers directly to a typed-value.

In fact, the compiler will transform this type definition into
something like:

```racket
(let ([Cons (λ (car cdr) (cval 'List 'Cons (λ (f) (f car cdr))))]
      [Nil               (cval 'List 'Nil  '())])
  <expression>)
```

Confused? I shall explain in details.

Type definition starts with the `T` keyword, and takes three
arguments. The first indicates the name of this type, in this case,
`List`. The second argument is a list of constructors, and the third
is the expression you want to evaluate within the environment with
this type defined. Each constructor is described in form of a list,
the first element in constructor definition indicates the name,
eg. `Cons`, and the rest, `car cdr`, indicate the arguments it would
take to construct such a type.

The compiler will establish a scope with these constructors defined as
lambdas. When the constructors are fed with sufficient arguments, it
will call the built-in function `cval` to construct a typed value. A
typed value has the following properties: the type, the constructor
used to construct this value, and a lambda with the constructor's
arguments stored and can be recalled anytime.

This lambda is an idea conceived by me alone, I don't know if there is
a name for this concept. When you need to manipulate the constructor
arguments' values, you pass a function with the same arity as the that
of the constructor to this lambda, then you will get each arguments
bound with specifc values accessible. Note that `Nil` does not have an
argument so there is certainly no where to recall it. Therefore, it
does not have a argument-value-storing-lambda.

I will make a small example on how to use it. Suppose you have a list
named `lst`, these expressions shows the ways to access the values in
it:

```racket
(fval (λ (car _) car) lst)            ;; like car
(fval (λ (_ cdr) cdr) lst)            ;; like cdr
(fval (λ (_ cdr)                      ;; like cadr
        (fval (λ (car _) car) cdr)
      lst))
```

Note the `fval` procedure takes its second argument, a typed-value,
extract the lambda stores constructor argument values. Then apply its
first argument, a given lambda, to the storing lambda to acquire these
values. Here putting a `_` in the place of a lambda arguments just
means to ignore it.


#### procedures, references, and keywords

Symbols in Loli are mostly the same as in other lisp faimily
languages, but there are small differences.

When you write symbols like `+`, `if`, or `trace`, they will compile
to `(p <#procedure xxx>)`, because those are procedures already
defined to be built-in.

Otherwise, these symbols will be compiled in a "reference" type, you
can think of this type in the same way you think of a "variable". For
example, `(+ a b)` will compile to something like `'((p <#procedure +> (r
a) (r b))`.

The term "keyword" may not be very proper but I don't know if there is
a better replacement. It is to indicates those symbol-like tokens that
are proceeded by Loli directly. This category includes:

* syntatic keywords, eg. `λ`, `T`
* lambda parameters, eg. `a`, `b` in `(λ (a b) ...)`
* some procedures' arguments, eg. `Cons` in `(ctorp Cons val)`
* type name, eg. `List` in `(T List (...) ...)`
* type constructor name, eg. `Cons`, in `(T List ((Cons a b) ...) ...)`
* type constructor arguments, eg. `a`, `b` in `(T List ((Cons a b) ...) ...)`


A keyword do never require a binding, because they are written
directly. *So you don't need to quote anything in Loli.*


### Built-in procedures

* `+`: takes two arguments, in integers, `(+ 2 3) => 5`
* `-`: takes two arguments, in integers, `(- 3 2) => 1`.
* `die`: takes an argument and ignore it, raise an error and terminate
  the evaluation.
* `trace`: takes two arguments, print the first and return the second.
  it does not interrupt the evaluation.
* `if`: takes a condition and two branches. the condition will
  evaluates to an integer, the value of `if` expression is its second
  argument if this integer is not `0`, otherwise the value will be is
  its third argument.
* `cval`: create a typed-value, you should never use this directly.
* `seq`: takes two arguments, force evaluates the first and return the
  second, just as the funcition named the same in haskell.
* `ctorp`: takes two arguments. the first argument is a constructor's
  name (keyword), and the second is an expression. it test if the
  second argument's value is constructed by this constructor, returns
  `1` or `0` indicates `true` and `false`.
* `fval`: takes two arguments, the first is a lambda and the second is
  a typed-value. it applies first argument to the
  constructor-value-storing lambda of the typed-value.



### Evaluation model

Loli uses lexical closures to implement lambdas. A lambda would
store the binding where it is created. When arguments are applied
to a lambda, they will be bound on the lambda's parameters, which is
based on the binding it stored, then the body will be executed with
this binding.

The term "environment" indicates a global binding in Loli. There are
two pre-defined environment usable in the source, `empty-env` and
`recur-env`. The first is completely empty and the second only has a
[Y combinator](http://en.wikipedia.org/wiki/Fixed-point_combinator#Y_combinator),
named `Y`, pre-defined, with which you can easily construct recursive
programs.



### Compile & Run Loli programs

**The most complete implemenation of Loli is in `lazy.rkt`!**

You need to compile the Loli programs using the `compile` function
defined in the source, for example:

```racket
(compile '(+ 1 2))
```

Fortunately, compiled programs are not completely
non-readable. Actually what the compiler does is pretty simple; it
only recognize the types for the tokens and expand the syntatic sugars
for lambdas, applications, and ADT defs.

Then you need to evaluate the compiled program in an
environment. Usually you will use `empty-env`, but you can also use
`recur-env` if you need and don't want to define the fix-point
combinator yourself.

There are two evaluation functions, `eval` and
`eval-force`. `eval-force` will guarantee to produce a
weak-head normal form
([WHNF](http://en.wikipedia.org/wiki/Lambda_calculus_definition#Weak_head_normal_form))
expression when it halts. So you should use `eval-force` if you want
to see a clear result like `(i 2)` rather than a complex reducible
expression
([redex](https://www.haskell.org/haskellwiki/Reducible_expression))<sup>[1]</sup>.

Evaluation function takes two arguments, a compiled Loli program and
an environment, below is a minimal working example:

```racket
(eval-force '(+ 1 2) empty-env)
```


**[1]**: Learn more about WHNF and redex on Heinrich Apfelmus's
    [article](https://hackhands.com/lazy-evaluation-works-haskell/). ([chinese version](http://shouya.github.io/blog/how-lazy-evaluation-works-in-haskell/))


### Tips

#### missing `Let` syntax

You can simulate `let` using lambdas,

```racket
(let ([a a-val]
      [b b-val]
      [c c-val])
  (+ a b c))
```

above code snippet in Scheme can be re-written in Loli as

```racket
((λ (a b c) (+ a b c))
 a-val
 b-val
 c-val)
```


#### missing recursion support

Loli does not support recursion directly, but you can have
[fix-point combinators](http://en.wikipedia.org/wiki/Fixed-point_combinator)!

With the environment `recur-env` you can use the Y combinator called
`Y`, to define recursive lambda and recursive data structures.

Below is an example defining a lambda that calculates a list's length:

```racket
(Y (λ (len xs) (if (ctorp Nil xs)
                   0
                   (+ 1 (len (fval (λ (hd tl) tl) xs))))))
```

In haskell, it's like to use the `fix` combinator:

```haskell
Y (\f xs -> if (xs == []) then 0 else 1 + f (tail xs))
```

You can read more about fix-point combinator elsewhere
if you are not very familiar with it.


Here shows an example definining a infinite list, some like `enumFrom n` in
Haskell.

```racket
(Y (λ (iter n) (Cons n (iter (+ n 1)))))
```

Another practical example definining a lambda to refer to the n-th
element in a list:

```racket
(Y (λ (f n xs)
     (if n
         (f (- n 1) (fval (λ (_ tl) tl) xs))
         (fval (λ (hd _) hd) xs))))
```


#### code reuse, ie. defining functions

Basically, you can use the `let` simulation to define a bunch of
functions and evaluate some expressions within this binding. But if
you consider doing this way makes code unreadable, you can use the
following method.

Although Loli does not aim to support function definition, you can
always do this in the Racket layer. Here is how,

You may define some variables to represent code snippets, values, or
lambdas. I will take the code from above:

```racket
(define prog-nth
  '(Y (λ (f n xs)
        (if n
            (f (- n 1) (fval (λ (_ tl) tl) xs))
            (fval (λ (hd _) hd) xs)))))

(define inf-list
  '(Y (λ (iter n) (Cons n (iter (+ n 1))))))

(define list-def
  '(λ (expr)
    (T L ((Nil) (Cons hd tl))
       expr)))
```

You can compose your program easily using [quasi-quotate and unquote](http://docs.racket-lang.org/reference/quasiquote.html) syntax in Racket.

```racket
(eval-force `(,list-def (,prog-nth 3 (,inf-list 2))))
```

The example above will produce `(i 5)`, as it's equivalent to the
haskell expression `[2..] !! 3`.

You're actually more powered than you have thought with Loli. Are you
feeling a little bit cooler now?
