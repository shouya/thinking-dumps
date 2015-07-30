#lang racket

(define entry car)
(define left-branch cadr)
(define right-branch caddr)
(define (make-tree ent l r) (list ent l r))


(define (lookup x set)
  (if (null? set) '()
      (case ([(= x (entry set)) (entry set)]
             [(< x (entry set)) (lookup x (left-branch set))]
             [(> x (entry set)) (lookup x (right-branch set))]))))
