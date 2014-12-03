#lang racket/base

(require scheme/mpair)
(require racket/function)
(require racket/list)

(define (eval-preliminary force?)
  (λ (expr env)
    (cond
     [(normal? expr) expr]
     [(redex? expr) (if force? (reduce expr env) expr)]
     [(appl? expr)
      (let ([ecar (eval-force (cadr expr) env)])
        (define eval-func
          (if force? eval-force eval))
        (define eval-lambda-opt
          (if force? eval-lambda-force eval-lambda))
        (cond
         [(λ? ecar)
          (eval-lambda-opt ecar (make-closure env (caddr expr)))]
         [(proc? ecar)
          (eval-proc (cadr ecar) (make-closure env (caddr expr)) env)]
         [else (error "unknown expression")]))])))

(define eval       (eval-preliminary #f))
(define eval-force (eval-preliminary #t))

(define (reduce expr env)
  (cond
   [(ref?  expr) (let ([val (follow-ref (cadr expr) env)])
                   (if (normal? val) val (resolve-closure val)))]
   [(λraw? expr) (make-lambda expr env)]
   [(closure? expr) (resolve-closure expr)]
   [else (error "not redex!")]))



;;; (Dynamic) closure related manipulations
(define (make-closure env expr)
  (list 'c env expr))

(define (resolve-closure c)
  (if (normal? c) c
      (begin
        (when (not (closure? c))
          (error "not a closure"))
        (let* ([env  (cadr  c)]
               [expr (caddr c)])
          (eval-force expr env)))))


;;; Environment manipulations

(define empty-env '())
(define (add-binding name val env)
  (mcons (cons name val)
         env))

(define (follow-ref name env)
  (maybe (findf (λ (b) (eq? (car b) name))
                (mlist->list env))
         cdr
         (λ () (error "undefined reference"))))


;;; Type predicates
(define (normal? expr)
  (memq (car expr)
        '(i p λ))) ;; type of expr which are regarded normal
(define (redex? expr)
  (memq (car expr)
        '(c r λraw)))


(define (type-predicate typechar)
  (λ (expr)  (eq? (car expr) typechar)))

(define ref?     (type-predicate 'r))
(define λ?       (type-predicate 'λ))
(define λraw?    (type-predicate 'λraw))
(define proc?    (type-predicate 'p))
(define closure? (type-predicate 'c))
(define int?     (type-predicate 'i))
(define appl?    (type-predicate 'appl))


;;; Built-in procedure related functions
(define (proc-exists? proc)
  (memq proc (map car proc-map)))

(define (make-proc p)
  (list 'p p))


;;; Value manipulations
(define val cadr)
(define normal-val (compose cadr resolve-closure))


;;; Lambda related functions
(define (make-lambda expr env)
  (list 'λ (cadr expr) (caddr expr) env))

(define (eval-lambda lamb arg)
  (let ([λparam cadr]
        [λbody caddr]
        [λenv cadddr])
    (let* ([param  (λparam lamb)]
           [body   (λbody  lamb)]
           [env    (λenv   lamb)]
           [newenv (add-binding param arg env)])
      (eval body newenv))))

(define (eval-lambda-force lamb arg)
  (let ([λparam cadr]
        [λbody caddr]
        [λenv cadddr])
    (let* ([param  (λparam lamb)]
           [body   (λbody  lamb)]
           [env    (λenv   lamb)]
           [newenv (add-binding param arg env)])
      (eval-force body newenv))))


;;; Built-in functions
(define (plus arg1 env1)
  (make-proc
   (λ (arg2 env2)
     (let ([a (val (eval-force arg1 env1))]
           [b (val (eval-force arg2 env2))])
       (list 'i (+ a b))))))

(define (die _)
  (error "you shouldn't see me here because i'm dead."))

(define (trace arg1 env1)
  (make-proc
   (λ (arg2 env2)
     (display (eval-force arg1 env1))
     (newline)
     (eval-force arg2 env2))))


(define (eval-proc foo args env)
  (foo args env))

(define (lookup-proc name)
  (maybe (findf (λ (proc) (eq? (car proc) name)) proc-map)
         cadr
         (λ () (error "procedure not found"))))

(define (maybe result just nothing)
  (if result
      (just result)
      (nothing)))


;; This function compiles lists like '(1 2 3 4) into
;;   '(appl (appl (appl 1 2) 3) 4)
(define (compile-fold-appl xs)
  (cond
   [(= (length xs) 2) (cons 'appl (map compile xs))]
   [(= (length xs) 1) (error "zero-argument λ not supported.")]
   [(= (length xs) 0) (error "what do you want to apply?")]
   [else (list 'appl
               (compile-fold-appl (take xs (- (length xs) 1)))
               (compile (last xs)))]))



;; This function compiles '(+ 1 (+ 2 3)) into
;;   '(appl (appl (p +) (i 1)) (appl (appl (p +) (i 2)) (i 3)))
(define (compile a)
  (cond
   [(and (symbol? a)
         (proc-exists? a)) (list 'p (lookup-proc a))]
   [(symbol? a) (list 'r a)]
   [(number? a) (list 'i a)]
   [(pair? a) (if (eq? 'λ (car a))
                  (list 'λraw (cadr a) (compile (caddr a)))
                  (compile-fold-appl a))]))



(define proc-map
  `([+ ,plus]
    [die ,die]
    [trace ,trace]
    ))

;; (eval (compile
;;        '(+ 1 (+ 2 3)))
;;       '())

;; (eval (compile
;;        '(((λ a (λ b (+ a b))) 1) 2)
;;        )
;;       '())

;; (eval (compile
;;        '((λ () (die))))
;;       '())


;(eval (compile
;       '((λ a (+ a a))
;         ((λ b (+ b b))
;          1))
;       ) empty-env)

;; Test delay
(display "---Test delay---\n")
(eval-force (compile
             '(((λ a (λ b a))
                1) s)
             ) empty-env)
;; this test fails if the unused `s` is evaluated.
;; only earger evaluation will make this test fail.


;; Test graph reduction
(display "---Test graph reduction---\n")
(eval-force (compile
             '((λ a (+ a a)) (trace 999 1))
             ) empty-env)
;; this test prints `999` for two times on
;; lazy language without proper graph reduction
;; optimization, it will print `999` once on earger
;; evaluation and lazy evaluation with graph reduction



;; (define dcenv (list->mlist '([k . (i 3)])))

;; (define env `([a . (i 1)]
;;               [b . ,(make-closure dcenv '(r k))]
;;               ))
;; (define menv (list->mlist env))

;; (follow-ref-force 'b menv)
