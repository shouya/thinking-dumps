#lang racket

(require racket/match)

(define (increment-symbol k)
  (string->symbol (string-append (symbol->string k) "1")))

;; compile cps directly
(define (compile-cps p k)
  (match p
    [(? integer?) `(,k ,p)]
    [(? symbol?)  `(,k ,p)]

    [(list 'if condition if-part else-part)
     (let ([bool-var (gensym 'b)]
           [if-part-cps (compile-cps if-part k)]
           [else-part-cps (compile-cps else-part k)])
       (compile-cps condition
                    `(λ (,bool-var)
                       (if ,bool-var
                           ,if-part-cps
                           ,else-part-cps))))]

    [(list 'begin expressions ...)
     (let* ([expr-symbols (map (λ (_) (gensym 'e)) expressions)]
            [last-symbol (last expr-symbols)]
            [procedure (λ (data accum)
                         (let ([expr (car data)]
                               [name (cdr data)])
                           (compile-cps
                            expr
                            `(λ (,name) ,accum))))]
            [data-list (zip expressions expr-symbols)])
       (foldr procedure `(,k ,last-symbol) data-list))]

    [(list 'λ (list parameters ...) body)
     (let* ([new-k (gensym 'k)]
            [body-cps (compile-cps body new-k)])
       `(,k (λ (,@parameters ,new-k)
              body-cps)))]

    [(list (? symbol? operator) operands ...)
     (let ([operand-symbols (map (λ (_) (gensym 'a)) operands)])
       (compile-cps `(begin ,operands)
                    `(,operator ,@operand-symbols)))]


    [(list operator operands ...)
     (let* ([operator-symbol (gensym 'f)]
            [operand-symbols (map (λ (_) (gensym 'a)) operands)]
            [application-expression `(,operator-symbol ,@operand-symbols)])
       (compile-cps operator
                    `(λ (,operator-symbol)
                       ,(compile-cps `(begin ,@operands)
                                     application-expression))))]

    ))



(define (zip l1 l2)
  (match* (l1 l2)
    [(`(,x ,xs ...) `(,y ,ys ...))
     (cons (cons x y)
           (zip xs ys))]
    [(_ _) '()]))


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

(print
 (compile-cps
  '(if 1 2 3)
  'k)
 )

;; (print
;;  (compile-cps
;;   '(if (1 < 2) (begin 3 4) 5)
;;   'k)
;;  )
