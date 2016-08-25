#lang racket

(require racket/match)

;; defining the tinyL
(define (compile p)
  (match p
    [(? integer?) (cons 'int p)]
    [(list 'if condition if-part else-part)
     (cons 'if (map compile (list condition if-part else-part)))]
    [(list op1 '+ op2)
     (cons '+ (map compile (list op1 op2)))]
    [(list op1 '< op2)
     (cons '< (map compile (list op1 op2)))]
  ))


;; compile cps directly
(define (compile-cps p)
  (match p
    [(? integer?) (λ (k) (k p))]

    [(list 'if condition if-part else-part)
     (λ (k)
      ((compile-cps condition)
       (λ (bool)
         (if bool
             ((compile-cps if-part)   k)
             ((compile-cps else-part) k)))))]

    [(list a '< b)
     (λ (k)
       ((compile-cps a)
        (λ (a-value)
          ((compile-cps b)
           (λ (b-value)
             (k (< a-value b-value)))))))]

    [(list a '+ b)
     (λ (k)
       ((compile-cps a)
        (λ (a-value)
          ((compile-cps b)
           (λ (b-value)
             (k (+ a-value b-value)))))))]

    [(list 'begin expressions ..1)
     (let ([hd (car expressions)]
           [tl (cdr expressions)])
       (λ (k)
         ((compile-cps hd)
          (λ (val)
            (if (null? tl)
                (k val)
                ((compile-cps (cons 'begin tl)) k))
            ))))]

    [(list 'λ (list parameters ...) body)
     1
     ;; TODO
     ]

    [(list 'print arg)
     (λ (k)
       ((compile-cps arg)
        (λ (val) (print val))))]

    ;; call-by-value
    ;; arg list evaluated from right to left (because of `foldl`)
    [(list operator operands ...)
     (λ (k) ((compile-cps operator)
             (λ (operator-cps)
               (let* ([operands-cps (map compile-cps operands)]
                      [folding (λ (cps carry) (cps (λ (v) (cons v carry))))]
                      [initial (λ (v) (cons v '()))]
                      [operand-list (foldl folding initial operands-cps)])
                 (apply-operands operator-cps operands-cps)))))]

    ))

(define (apply-operands operator-cps operands-cps)
  ;; TODO
  '())

(define example-program-1
  '(+ 2 1))
(define example-program-2
  '(print (+ 2 1)))
(define example-program-3
  '((λ (x) (print (+ x 1))) 2))
(define example-program-4
  '((λ (x) (if (x < 10)
               (print (+ x 1))
               (print (+ x 2))))
    12))

((compile-cps
  '(if (1 < 2) (begin 3 4) 5)
  ) print)
