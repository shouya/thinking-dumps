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


TL;DR: Read the source of Loli in `lazy.rkt` and the sample Loli programs in the
bottom of the source file. Execute the source in drracket or CLI to
see the result.

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
The syntax of loli is basicall s-expressions, expressed as a quoted
list in Racket.


#### lambda definition

You may define a lambda that perform a simplest plus operation like this:

```racket
(λ (a b) (+ a b))
```

for one argument lambda, the paren is optional, ie. you can write
code like this:

```racket
(λ a (+ 1 a))
```

Loli lambdas always curry, that is to say,

```racket
(λ (a b) (+ a b))
```

is just a syntatic sugar of writing

```racket
(λ (a) (λ (b) (+ a b)))
```

Because of purity, zero argument lambda is not allowed.

*compiler details:* all syntatic sugars, including multi-argument
 lambda and multiple application, are expanded in the compiling
 phase. a lambda definition will be expanded to a `λraw` typed
 expression, which will become a real `λ` when it is being evaluated.


#### application

You can apply values on procedures, as well as lambdas,

```racket
(+ 1 1)
((λ (a b) (+ a b)) 1 2)
```

Because loli curries, applying multiple values is also just a syntatic
sugar:

```racket
(+ 1 1)
```

is equivalent to:

```racket
((+ 1) 1)
```


#### algebraic data type definition

For example you want to describe a list, you will use the following
ADT definition in Haskell:

```haskell
data List a = Nil
            | Cons a (List a)
```

Notice that when you use type constructors like `Cons`,
it behaves just like a function. It takes curried arguments, and
results in a value with `List` type.

In Loli, constructors *are* lambdas, also they yield a value in a
defined type. We would call such values as 'typed-values' (V).

In Loli, types are dynamic. You don't need to specify a type variable
when you are defining an ADT.

Besides, because of the functionality, Loli does not provide a mutable
environment, so you can't `define` a value, or a type, but you can
rather `let` something.

So let me `let` a simpliest `List` type in Loli:

```racket
(T List ((Cons car cdr)
         (Nil a))
  <expression>)
```

`Nil`, although not necessary, still requires an argument because it
needs to be as a lambda. (remember? c-tors *are* lambdas)
*(this is actually a deficiency, I will fix it later)*

In fact, the compiler will transform this type definition into
something like:

```racket
(let ([Cons (λ (car cdr) (cval 'List 'Cons (λ (f) (f car cdr))))]
      [Nil  (λ (a)       (cval 'List 'Nil  (λ (f) (f a))))])
  <expression>)
```

Confused? I shall explain in details.

Type definition starts with the `T` keyword, and takes three
arguments. The first indicates the name of this type, in this case,
`List`. The second argument is a list of constructors, and third is
the expression you want to execute within the environment with this
type defined. Each constructor is described in form of a list, the
first elements indicates the name, and the rest indicate the
arguments it would take to construct such a type.

The compiler will establish a scope with these constructors defined as
lambdas. When the constructors are fed with sufficient arguments, it
will call the built-in function `cval` to construct a typed-value, a
typed value has the following properties, the type, the constructor
used to construct this value, and a lambda with the constructor's
arguments stored and can be recalled anytime.

This lambda is an idea conceived by me, I don't know if there is a
name of this concept. When you need to manipulate the constructor
arguments' values, you pass a function with the same arity as the
constructor to this lambda, and you will get each arguments
accessible. I will make a small example on how to use it.

Suppose you have a list named `lst`, these expressions shows the way
to access the values of it:

```racket
(fval (λ (car _) car) lst)            ;; like car
(fval (λ (_ cdr) cdr) lst)            ;; like cdr
(fval (λ (_ cdr)                      ;; like cadr
        (fval (λ (car _) car) cdr)
      lst))
```

Note the `fval` procedures takes its second argument, a typed-value,
extract the lambda stores constructor argument values, and apply the first
argument, a given lambda to it to acquire these values. Here putting a
`_` in the place of a lambda arguments just means to ignore it.


#### procedures, references, and keywords

Writing a symbol in Loli is mostly the same as in other lisp
languages, but there are small differences.

When you write symbols like `+`, `if`, or `trace`, it will compiles to
`(p <#procedure xxx>)`. Because those are procedures already defined
to be built in.

Otherwise, these symbols will be compiled in a "reference" type, you
can think of this type in the same way you think of a "variable". For
example, `(` will compile to something like `'((p <#procedure +> (r
a) (r b))`.

The term "keyword" may not be very proper but I don't know if there is
a better one. It is to indicates those symbol-like tokens that are
proceeded by Loli directly. This category includes:

* syntatic keywords, eg. `λ`, `T`
* lambda parameters, eg. `a`, `b` in `(λ (a b) ...)`
* some procedures' arguments, eg. `Cons` in `(ctorp Cons val)`
* type name, eg. `List` in `(T List (...) ...)`
* type constructors definitions, eg. `(Cons a b)` in `(T List ((Cons a b) ...) ...)`

A keyword do never require a binding, because they are used
directly. *So you don't need to quote anything in Loli.*


### Built-in procedures

* `+`: takes two arguments, in integers, plus them.
* `-`: takes two arguments, in integers, `(- 3 2) => 1`.
* `die`: takes an argument and ignore it, raise an error and terminate
  the execution.
* `trace`: takes two arguments, print the first and return the second,
  does not interrupt the execution.
* `if`: takes a condition and two branches, The condition will
  evaluates to an integer, the value of `if` expression is its second
  argument if the integer is not `0`, otherwise the value is its third
  argument.
* `cval`: create a typed-value, you should not use this directly.
* `seq`: takes two arguments, force evaluates the first and return the
  second, just as the same funcition in haskell.
* `ctorp`: takes two arguments. the first argument is a constructor's
  name (keyword), and test if the second argument's value is
  constructed by this constructor.
* `fval`: takes two arguments, the first is a lambda and the second is
  a typed-value. it applies first argument to the
  constructor-value-storing lambda of the typed-value.


### Evaluation model

Loli's uses lexical closures to implement lambdas. A lambda would
store the binding of where it is created. When arguments are applied
to a lambda, they will be bound on the lambda's parameters, based on
the binding it has stored, then body will be executed with such
binding.

The term "environment" indicates a global binding in Loli. There are
two pre-defined environment usable in the source, `empty-env` and
`recur-env`. The first is completely empty and the second only has
[Y combinator](http://en.wikipedia.org/wiki/Fixed-point_combinator#Y_combinator),
named `Y`, pre-defined, so you can easily construct recursive programs.


### Compile & Run Loli programs

**The most complete implemenation of Loli is in `lazy.rkt`!*

You need to compile the Loli programs using the `compile` function
defined in the languages, for example:

```racket
(compile '(+ 1 2))
```

A compiled program is not completely non-readable. Actually the
compiler is pretty simple; it only does type recognition for tokens
and expand the syntatic sugars for lambdas, applications, and ADT defs.


### Tips

You can simulate `let` using lambdas,

```racket
(let ([a a-val]
      [b b-val]
      [c c-val])
  (+ a b c))
```

can be written as

```racket
((λ (a b c) (+ a b c))
 a-val
 b-val
 c-val)
```
