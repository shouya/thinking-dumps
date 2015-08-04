
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

;; here's the impl

(define (make-poly variable term-list)
  (cons variable term-list))
(define (variable p) (car p))
(define (term-list p) (cdr p))
;; continued on next page

(define (adjoin-term term term-list)
  (if (=zero? (order term))
      (cons (coeff term) term-list)
      (cons (car term-list)
            (adjoin-term (make-term (- (order term) 1)
                                    (coeff term))
                         (cdr term-list)))))

(define (the-empty-termlist) '())
(define (first-term term-list)
  (make-term (- (length term-list) 1)
             (car term-list)))
(define (rest-terms term-list) (cdr term-list))
(define (empty-termlist? term-list) (null? term-list))
(define (make-term order coeff) (cons order coeff))
(define (order term) (car term))
(define (coeff term) (cdr term))
