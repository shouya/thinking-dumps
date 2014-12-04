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
important, it's adorable. I call she `loli`, suggested by
[@codeotakuchiyan](https://twitter.com/codeotakuchiyan).

![Loli's - Moegirl Wiki](http://static.mengniang.org/common/c/c1/Roukyubu.jpg)

Loli is a lisp dialect that aims to be in research purpose, she so far implements
[lazy evaluation](http://en.wikipedia.org/wiki/Lazy_evaluation) and
[algebraic data types](http://en.wikipedia.org/wiki/Algebraic_data_type),
other features are not planned yet.
