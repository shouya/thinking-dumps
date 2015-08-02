;; my custmozed data directed library

#lang racket

(provide (all-defined-out))

(define proc-table (make-hash))
(define coercion-table (make-hash))

(define (type ) type)



(define (put name types proc)
  (if (hash-ref proc-table name)
      (hash-set! (hash-ref name) types proc)
      (hash-set! name (hash types proc))))
(define (get name types)
  (if (hash-ref proc-table name)
      (hash-ref (hash-ref name) types)
      (error "no such procedure")))


(define (put-coercion from to proc)
  (if (hash-ref coercion-table from)
      (hash-set! (hash-ref from) to proc)
      (hash-set! from (hash to proc))))
(define (get-coercion from to)
  (if (hash-ref coercion-table from)
      (hash-ref (hash-ref from) to)
      (error "no such procedure")))


(define attach-tag cons) ; (type value)
(define type-tag car)
(define contents cdr)


(define (apply-generic op . args)
  (define type-tags (map type-tag args))
  (define proc (get op type-tags))

  (if proc (apply proc (map contents args))
      (match* (type-tags args)
        [((list a1 a2) (list t1 t2))
         (let ([t1->t2 (get-coercion t1 t2)]
               [t2->t1 (get-coercion t2 t1)])
           (cond [t1->t2 (apply-generic op (t1->t2 a1) a2)]
                 [t2->t1 (apply-generic op a1 (t2->t1 a2))]
                 [else (error "no coercion for the types")]))]
        [(_ _) (error "not regular procedure")])))
