A CPS compiler for a tiny language.

## Brief specification

**Expressions:**

- integer literals
- `(a + b)`, returns the sum of `a` and `b`
- `(a < b)`, compare `a` and `b`, returns a boolean value, mainly used in if-condition
- `(if cond if-part else-part)`
- `(print value)`, print an integer
- `(begin expressions ...)`, evaluate all expressions and return the result of the last one
- `(λ (parameters ...) body)`, an unevaluated lambda, return reduced body when evaluated
- `(foo arguments ...)`, evaluate lambda `foo` and then apply it with the evaluated `arguments`
- `(return val)`, early return from a lambda


**Proposed features:**

- throw and catch


**Description:**

This language follows the call-by-value semantics. i.e. In a lambda application process, arguments are evaluated before being passed to lambdas.

Lambda arguments are evaluated from right to left.

## Available functions

- `(compile-cps expr)`, compile `expr` of the tiny language into a native racket CPS program

## Examples

TODO

## References

- https://en.wikipedia.org/wiki/Continuation-passing_style
