#lang racket

;; first please note that the type tower is not a tree but a
;; acyclic graph. for a node there could be not a single parent.
;;

(provide (all-defined-out))

(define hierarchy (make-hash)) ; child -> [parent] mapping

(define (define-polygon-hierarchies)
  (define (set-parent child parent)
    (if (hash-has-key? hierarchy child)
        (hash-update! hierarchy child (λ (ps) (cons parent ps)))
        (hash-set! hierarchy child (list parent))))

  (set-parent 'square 'rectangle)
  (set-parent 'square 'rhombus)
  (set-parent 'rectangle 'parallelogram)
  (set-parent 'rhombus 'parallelogram)
  (set-parent 'parallelogram 'trapezoid)
  (set-parent 'trapezoid 'quadrilateral)
  (set-parent 'rhombus 'kite)
  (set-parent 'kite 'quadrilateral)
  (set-parent 'quadrilateral 'polygon)
  (set-parent 'isosceles-right-triangle 'isosceles-triangle)
  (set-parent 'isosceles-right-triangle 'right-triangle)
  (set-parent 'equilateral-triangle 'isosceles-triangle)
  (set-parent 'isosceles-triangle 'triangle)
  (set-parent 'right-triangle 'triangle)
  (set-parent 'triangle 'polygon))

(define (define-number-hierarchies)
  (define (set-parent child parent)
    (if (hash-has-key? hierarchy child)
        (hash-update! hierarchy child (λ (ps) (cons parent ps)))
        (hash-set! hierarchy child (list parent))))

  (set-parent 'number 'rational)
  (set-parent 'rational 'complex))


(define (raise child)
  (if (hash-has-key? hierarchy child)
      (car (hash-ref hierarchy child))
      (error "parent not defined for ~a" child)))
