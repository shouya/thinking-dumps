#lang racket/base


(define (eval expr)
  (if (normal? expr) expr
      (let ([ecar (eval (car expr))])
        (if (built-in-proc? ecar)
            (eval-built-in-proc (lookup-built-in-proc (cadr ecar))
                                (map eval (cdr expr)))
        (error "unknown expression")))))

(define (normal? expr)
  (member (car expr) ;; type of expr
          '(i λ)))

(define (plus xs)
  (list 'i (foldl + 0 (map cadr xs))))

(define (built-in-proc? proc)
  (member (cadr proc) (map car proc-maps)))

(define (eval-built-in-proc foo args)
  (foo args))

(define (lookup-built-in-proc name)
  (let ([proc (findf (λ (proc) (eq? (car proc) name)) proc-maps)])
    (if proc
        (cadr proc)
        (error "procedure not found"))))
   
;; This function compiles '(+ 1 (+ 2 3)) into '((λ +) (i 1) ((λ +) (i 2) (i 3))
(define (compile a)
  (cond
    [(symbol? a) (list 'λ a)]
    [(number? a) (list 'i a)]
    [(pair? a) (map compile a)]))
                 
  
(define proc-maps
  `([+ ,plus]))

(eval (compile
       '(+ 1 (+ 2 3))))


  