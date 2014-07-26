# Algebra of Algebraic Data Types

## Resource 1

* [The Algebra of Algebraic Data Types, Part 1](https://chris-taylor.github.io/blog/2013/02/10/the-algebra-of-algebraic-data-types/)
* [The Algebra of Algebraic Data Types, Part 2](https://chris-taylor.github.io/blog/2013/02/11/the-algebra-of-algebraic-data-types-part-ii/)
* [The Algebra of Algebraic Data Types, Part 3](https://chris-taylor.github.io/blog/2013/02/13/the-algebra-of-algebraic-data-types-part-iii/)


### Exercise 1

Exercise: Code up the zipper for binary trees, remembering that a
zipper is a one-hole context paired with data. You’ll need to write
functions left and right to take the left or right path at a
particular node, and up to go back up the tree.

Solution: `treezipper.hs`
See Also: `listzipper.hs`

### Exercise 2
Exercise: Rose trees are trees with arbitrarily many branches from
each node. In Haskell you would define them by

```haskell
data Rose a = Rose a [Rose a]
```

What does a rose tree zipper look like?

Solution: `rosezipper.hs`
