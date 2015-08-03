(require "data-directed.rkt")
(require "2.83.rkt") ; raise

(define-number-hierarchies)

;; tell where t1 is a (grand)*child of t2
(define (child-of? t1 t2)
  (if (eq? t1 t2)
      #t
      (child-of? (raise t1) t2)))

(define (successive-coerce t1 t2 val)
  (if (eq? t1 t2) val
      (successive-coerce (raise t1)
                         t2
                         ((get-coercion t1 (raise t1)) val))))

(define (apply-generic-1 op . args)
  (define type-tags (map type-tag args))
  (define proc (get op type-tags))

  (if proc (apply proc (map contents args))
      (match* (type-tags args)
        [((list a1 a2) (list t1 t2))
         (let ([a1_ (cond [(child-of? t1 t2) (successive-coerce t1 t2 a1)]
                          [else a1])]
               [a2_ (cond [(child-of? t2 t1) (successive-coerce t2 t1 a2)]
                          [else a2])])
           (apply-generic-1 op a1_ a2_))]
        [(_ _) (error "not regular procedure")])))
