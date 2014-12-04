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


**lambda definition**

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
```.

Because of purity, zero argument lambda is not allowed.

*compiler details:* all syntatic sugars, including multi-argument
 lambda and multiple application, are expanded in the compiling
 phase. a lambda definition will be expanded to a `λraw` typed
 expression, which will become a real `λ` when it is being evaluated.



**application**

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


**algebraic data type definition**

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
accessible. I will make a small example on how to use it:

Suppose you have a list named `lst`, these expressions shows the way
to access the values of it:

```racket
(fval (λ (car _) car) lst)            ;; like car
(fval (λ (_ cdr) cdr) lst)            ;; like cdr
(fval (λ (_ cdr)                      ;; like cadr
        (fval (λ (car _) car) cdr)
      lst))
```

Putting a `_` in the place of a lambda arguments means to ignore it.


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
