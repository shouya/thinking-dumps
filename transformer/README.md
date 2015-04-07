## A monad transformer practice.

[Monad Transformers: Step-By-Step](http://www.cs.virginia.edu/~wh5a/personal/Transformers.pdf)


This program implements a small interpreter with various features by
nesting different monad transformer:

* error handling: `ExceptT String`
* implicit environment param: `ReaderT Env`
* instruction counting: `StateT Integer`
* logging: `WriterT [String]`
* chatterbox-ization: `IO`


It finally looks like:

```haskell
type Eval a = WriterT [String] (StateT Integer (ReaderT Env (ExceptT String IO))) a
```



Other helpful resources:

* [Why is there no IO transformer in Haskell?](https://stackoverflow.com/questions/13056663/why-is-there-no-io-transformer-in-haskell)
