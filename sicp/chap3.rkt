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


;; ex 3.3 account with password
(define (make-account balance password)
  (define (withdraw amount)
    (if (>= balance amount)
        (set! balance (- balance amount))
        (error "insufficient balance")))
  (define (deposit amount)
    (set! balance (+ balance amount)))

  (define (password-correct? pwd) (eq? pwd password))

  (λ (password op)
    (if (password-correct? password)
        (cond [(eq? op 'withdraw) withdraw]
              [(eq? op 'deposit)  deposit])
        (error "wrong password!"))))
