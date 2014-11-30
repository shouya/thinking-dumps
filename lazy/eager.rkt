#lang racket/base

(define (eval expr env)
  (cond
    [(normal? expr) expr]
    [(lambda? expr) (create-lambda expr env)]
    [(ref? expr) (follow-ref (cadr expr) env)]
    [else (let ([ecar (eval (car expr) env)])
            (cond
              [(lambda? ecar)
               (eval-lambda ecar
                            (map (eval-env env) (cdr expr)))]
              [(proc? (cadr ecar))
               (eval-proc (lookup-proc (cadr ecar))
                          (map (eval-env env) (cdr expr)))]
              [else (error "unknown expression")]))]))


(define (eval-env env)
  (λ (x) (eval x env)))

(define (normal? expr)
  (memq (car expr) '(i p))) ;; type of expr

(define (ref? expr)
  ((car expr) . eq? . 'r))

(define (lambda? expr)
  ((car expr) . eq? . 'λ))

(define (follow-ref name env)
  (maybe (findf (λ (b) (eq? (car b) name)) env)
         cadr
         (λ () (error "undefined reference"))))

(define (create-lambda expr env)
  (list 'λ (cadr expr) (caddr expr) env))

(define (eval-lambda lamb arg)
  (let ([λparam cadr]
        [λbody caddr]
        [λenv cadddr])
    (let* ([param (λparam lamb)]
           [body (λbody lamb)]
           [env (cons `(,param . ,arg)
                      (λenv lamb))])
      (eval body env))))


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
       '(((λ a (λ b (+ a b))) 1) 2)
       )
      '())



