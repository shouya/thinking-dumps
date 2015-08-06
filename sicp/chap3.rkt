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
#;
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


;; ex 3.4
(define (make-account balance password)
  (define (withdraw amount)
    (if (>= balance amount)
        (set! balance (- balance amount))
        (error "insufficient balance")))
  (define (deposit amount)
    (set! balance (+ balance amount)))
  (define mistake-count 0)

  (define (password-correct? pwd) (eq? pwd password))

  (λ (password op)
    (if (password-correct? password)
        (begin
          (set! mistake-count 0)
          (cond [(eq? op 'withdraw) withdraw]
                [(eq? op 'deposit)  deposit]))
        (begin
          (set! mistake-count (+ mistake-count 1))
          (if (> mistake-count 7)
              (error "☎︎110") ; or call-the-cops
              (error "wrong password!"))))))


;; ex 3.5 monte carlo integration
(define (monte-carlo trials experiment)
  (define (iter trials-remaining trials-passed)
    (cond ((= trials-remaining 0)
           (/ trials-passed trials))
          ((experiment)
           (iter (- trials-remaining 1) (+ trials-passed 1)))
          (else
           (iter (- trials-remaining 1) trials-passed))))
  (iter trials 0))

(define (random-in-range low high)
  (let ((range (- high low)))
    (+ low (* (random) range))))

(define (estimate-integral p x1 x2 y1 y2 trials)
  (define (new-p)
    (let ([x (random-in-range x1 x2)]
          [y (random-in-range y1 y2)])
      (p x y)))
  (monte-carlo trials new-p))
