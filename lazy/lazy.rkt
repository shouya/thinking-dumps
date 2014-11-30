#lang racket

(define eval eval!)

(define (eval! expr env)
  (case (car expr)
    ['+ (eval (+ (cadr expr) (caddr expr)))]
    ['except (error "aha! mia G point got touched!")]
    ))