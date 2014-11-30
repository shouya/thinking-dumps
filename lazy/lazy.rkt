#lang racket

(define (eval! expr env)
  (undefined))

(define eval eval!)

(define (built-in-op? sym)
  (member sym (map car built-in-symbol-map)))


(define (normal-form? expr)
  (case (type-of expr)
    ['num  #t]
    ['λ    #t]
    ['appl #f]))

(define (getval expr)
  (if (normal-form? expr)
      (cdr expr)
      (error "not value in normal form")))


(define type-of car)

(define my-prog
  '[appl (λ '+) (num 1) (num 2)])

(define built-in-symbol-map
  '([+      (λ (rest) (+ (getval (eval (cadr rest)))
                         (getval (eval (cadr rest)))))]
    [except (λ (rest) (error "aha! mia G point got touched!"))]))
  
(define (undefined) (error "meow"))