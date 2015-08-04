#lang racket

(require "data-directed.rkt")
(provide install-=zero?-package)

(define (install-=zero?-package)
  ;; scheme number package
  (define (=zero?-scheme-number x)
    (eqv? x 0))

  (put '=zero? '(scheme-number) =zero?-scheme-number)


  ;; rational number package

  (define (=zero?-rational-number x)
    (match x
      [(list num den) (eqv? num 0)]))

  (put '=zero? '(rational) =zero?-rational-number)


  ;; complex number package

  (define (=zero?-complex-number x)
    (let ([a (real-part x)] [b (imag-part x)])
      (and (eqv? a 0) (eqv? b 0))))

  (put '=zero? '(complex) =zero?-complex-number)


  (define (=zero? x) (apply-generic '=zero? x))
  'done)
