#lang racket

;; a.

;; if we call exp with two complex number args,
;; then the first complex number will be converted
;; into a complex number, which is itself.
;; and then apply-generic will be called with the
;; same args. this will result in an infinite loop.


;; b.

;; first of all, i think apply-generic is defined
;; to have some problem. it only consider apply args to
;; functions that are defined with exact corresponding
;; types. this is good. however, it assumes that all binary
;; functions SHOULD be defined to eat the same type args.
;; this is not quite true because the argument types could
;; vary. the coercion should not just unify these two types
;; but also consider the function with what type signatures
;; are defined and try to find a closest yet more generic
;; definition.
;;
;; i think louis didn't do this wrong because it's natural,
;; though trivial, to have the coercions from a type to itself.
;;


;; c.

;; as i mentioned in b., i don't think that only patching to
;; tolerate this special case would be a very smart idea.
;; because there is something wrong with apply-generic and this
;; part deserves a rewrite.
;;
;; however, simply the given task wasn't hard. one only need to
;; test for if the two types are the same at
;;
;;           (if (eqv? (length args) 2) <here> (error xxx))
;;
;; (if (equal? t1 t2) (error "this op isn't defined") ...)
;;
