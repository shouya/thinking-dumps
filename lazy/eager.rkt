#lang racket/base

(define (eval expr env)
  (if (normal? expr) expr
      (if (ref? expr) (follow-ref (cadr expr) env)
          (let ([ecar (eval (car expr) env)])
            (if (proc? (cadr ecar))
                (eval-proc (lookup-proc (cadr ecar))
                           (map (λ (x) (eval x env)) (cdr expr)))
                (if (lambda? ecar)
                    (eval-lambda ecar (map (λ (x) (eval x env)) (cdr expr)) env)
                    (error "unknown expression")))))))

(define (normal? expr)
  (memq (car expr) ;; type of expr
          '(i p λ)))

(define (ref? expr)
  ((car expr) . eq? . 'r))

(define (lambda? expr)
  ((car expr) . eq? . 'λ))

(define (follow-ref name env)
  (maybe (findf (λ (b) (eq? (car b) name)) env)
         cadr
         (λ () (error "undefined reference"))))

(define (eval-lambda lamb arg env)
  (let ([λparam cadr]
        [λbody caddr]
        [λenv env])
    (let ([param (λparam lamb)]
          [body (λbody lamb)])
      (set! λenv (cons `(,param . ,arg) env))
      (eval body λenv))))
  

(define (plus xs)
  (list 'i (foldl + 0 (map val xs))))

(define val cadr)  ;; extracting value, e.g. '(i 1) -> 1

(define (proc? proc)
  (memq proc (map car proc-map)))

(define (eval-proc foo args)
  (foo args))

(define (lookup-proc name)
  (maybe (findf (λ (proc) (eq? (car proc) name)) proc-map)
         cadr
         (λ () (error "procedure not found"))))

(define (maybe result just nothing)
  (if result
      (just result)
      (nothing)))

;; This function compiles '(+ 1 (+ 2 3)) into '((p +) (i 1) ((p +) (i 2) (i 3))
(define (compile a)
  (cond
    [(and (symbol? a)
          (proc? a)) (list 'p a)]
    [(symbol? a) (list 'r a)]
    [(number? a) (list 'i a)]
    [(pair? a) (if (eq? 'λ (car a))
                   (list 'λ (cadr a) (compile (caddr a)))
                   (map compile a))]))



(define proc-map
  `([+ ,plus]))

; (eval (compile
;        '(+ 1 (+ 2 3)))
;       '())

(eval (compile
       '((λ a (+ a a)) 1))
      '())



