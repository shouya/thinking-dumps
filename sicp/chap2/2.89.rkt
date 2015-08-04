
;; dense polynomials are polynomial whose coefficient
;; for most terms are not zero. (in contrast of sparse)
;;

;; for example we want to express x^3+6x^2+1,
;; which is relatively dense. for our current repr,
;; it should be something look like:

'((3 1) (2 6) (0 1))

;; so we can make it easier by ignoring the order,
;; given they are in a descending order and are
;; dense. we can represent the same polynomial more
;; efficiently:

'(1 6 0 1)

;; for which we only record the coefficients and
;; we have order(p) = length(p) - 1
;;
