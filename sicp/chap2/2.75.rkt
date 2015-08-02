#lang racket

;; 2.75 implement `make-from-mag-ang` in message passing style

(define (make-from-mag-ang mag ang)
  (λ (req)
    (case req
      [(real-part) (* mag (cos ang))]
      [(imag-part) (* mag (sin ang))]
      [(magnitude) mag]
      [(angle)     ang]
      [else        (error "unknown!")])))
