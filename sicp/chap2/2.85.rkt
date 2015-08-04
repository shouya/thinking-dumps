#lang racket

(require "data-directed.rkt")

;; this needs us to revise the definition of hierarchy table
;; because the previous implementation was in was a singly-linked
;; hash-table towards the most generic type. we now need it to be
;; able to trace the link down. it would need an extra hierarchy
;; table.
;;
;; i'll do this by rewrite the table from 2.83

(define hierarchy-up (make-hash))   ; child -> [parent] mapping
(define hierarchy-down (make-hash)) ; parent -> [child] mapping

(define (set-parent child parent)
  (begin
    (if (hash-has-key? hierarchy-up child)
        (hash-update! hierarchy-up child (λ (ps) (cons parent ps)))
        (hash-set! hierarchy-up child (list parent)))
    (if (hash-has-key? hierarchy-down parent)
        (hash-update! hierarchy-down parent (λ (ps) (cons child ps)))
        (hash-set! hierarchy-down parent (list child)))))

(define (define-number-hierarchies)
  (set-parent 'number 'rational)
  (set-parent 'rational 'complex))


(define (raise child)
  (if (hash-has-key? hierarchy-up child)
      (car (hash-ref hierarchy-up child))
      (error "parent not defined for ~a" child)))

(define (project parent)
  (if (hash-has-key? hierarchy-down parent)
      (car (hash-ref hierarchy-down parent))
      '())) ; indicates no child-type

(define (unit val this-type child-type)
  (define this->child (get-coercion this-type child-type))
  (define child->this (get-coercion child-type this-type))
  (child->this (this->child val)))

(define (drop val)
  (define this-type  (type-tag val))
  (define child-type (project this-type))

  (if child-type
      (let ([val' (unit val this-type child-type)])
        (if (equal? val' val)
            (drop val)
            val))
      val) ; leave unchanged
  )
