
;; scheme number package

(define (equ-scheme-number x y)
  (eqv? x y))

(put 'equ '(scheme-number scheme-number) equ-scheme-number)


;; rational number package

(define (equ-rational-number x y)
  (match* (x y)
    [((list num1 den1) (list num2 den2))
     (eqv? (* den1 num2) (* den2 num1))]))

(put 'equ '(rational rational) equ-rational-number)


;; complex number package

(define (equ-complex-number x y)
  (let ([a1 (real-part x)] [a2 (real-part y)]
        [b1 (imag-part x)] [b2 (imag-part y)])
    (and (eqv? a1 a2)
         (eqv? b1 b2))))

(put 'equ '(complex complex) equ-complex-number)
