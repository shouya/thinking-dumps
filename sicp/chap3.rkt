#lang racket

;; ex 3.1 make an accumulator
(define (make-accumulator n)
  (define x n)
  (λ (amount)
    (begin (set! x (+ x amount))
           x)))

;; ex 3.2 make function monitor wrapper
(define (make-monitored func)
  (define call-count 0)
  (λ xs (if (and (not (null? xs))
                 (= (length xs) 1)
                 (eq? 'how-many-calls? (car xs)))
            call-count
            (apply func xs))))
