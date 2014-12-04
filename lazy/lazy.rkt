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
        (define (reduce-opt val) (if force? (reduce val env) val))
        (cond
         [(λ? ecar)
          (reduce-opt (eval-lambda ecar (make-closure env (caddr expr))))]
         [(proc? ecar)
          (reduce-opt (eval-proc ecar (make-closure env (caddr expr))))]
         [else (error "unknown expression")]))])))

(define eval       (eval-preliminary #f))
(define eval-force (eval-preliminary #t))

(define (reduce expr env)
  (let ([result (cond
                 [(ref?  expr) (follow-ref-force (cadr expr) env)]
                 [(λraw? expr) (make-lambda expr env)]
                 [(closure? expr) (resolve-closure expr)]
                 [(normal? expr) expr]
                 [else (error "neither redex nor normal!")])])
    (if (redex? result)
        (reduce result env)
        result)))




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

;; This function modifies the `env`
(define (setval name newval env)
  (if (null? env)
      (error "name not defined")
      (if (eq? name (car (mcar env)))
          (set-mcar! env (cons name newval))
          (setval name newval (mcdr env)))))


;; This function appears pure from the outside
(define (follow-ref-force name env)
  (define refval (follow-ref name env))
  (if (normal? refval)
      refval
      (let ([resolved-val (reduce refval env)])
        (setval name resolved-val env)
        resolved-val)))



;;; Type predicates
(define (normal? expr) ; types of expr which are regarded normal (precisely, WHNF)
  (memq (car expr)
        '(i p λ V)))
(define (redex? expr)
  (memq (car expr)
        '(c r λraw)))


(define (type-predicate typechar)
  (λ (expr) (eq? (car expr) typechar)))

(define ref?       (type-predicate 'r))
(define λ?         (type-predicate 'λ))
(define λraw?      (type-predicate 'λraw))
(define proc?      (type-predicate 'p))
(define closure?   (type-predicate 'c))
(define int?       (type-predicate 'i))
(define appl?      (type-predicate 'appl))
(define typed-val? (type-predicate 'V))



;;; Built-in procedure related functions
(define (proc-exists? proc)
  (memq proc (map car proc-map)))

(define (make-proc p)
  (list 'p p))
(define (make-int v)
  (list 'i v))
(define (make-appl f a)
  (list 'appl f a))


;;; Value manipulations
(define val cadr)
(define normal-val (compose cadr resolve-closure))

(define (extract-keyword val)
  (cond
   [(ref? val)     (cadr val)]
   [(closure? val) (cadr (caddr val))]
   [else           (error "not a keyword")]))

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
      (make-closure newenv body))))


;;; Type constructors
;;
;; representation of typed values:
;;     '(V <type> <ctor> <valλ>)
;; Example:
;;   assume '(T t [c1 a b] expr) is defined
;;   (c1 2 3) will yield
;;     '(V t c1 (λ f (f 2 3)))

(define (construct-value type ctor valλ)
  (list 'V type ctor valλ))

(define (cval-proc type)
  (define Ttype (caddr type))
  (make-proc
   (λ (ctor)
     (define Tctor (caddr ctor))
     (make-proc
      (λ (valλ)
        (let ([Ttypekw (extract-keyword Ttype)]
              [Tctorkw (extract-keyword Tctor)]
              [Tvalλ   (resolve-closure valλ)])
          (construct-value Ttypekw Tctorkw Tvalλ)))))))


;;; Built-in functions
(define (plus arg1)
  (make-proc
   (λ (arg2)
     (let ([a (val (resolve-closure arg1))]
           [b (val (resolve-closure arg2))])
       (make-int (+ a b))))))

(define (die _)
  (error "you shouldn't see me here because i'm dead."))

(define (trace arg1)
  (make-proc
   (λ (arg2)
     (display (resolve-closure arg1))
     (newline)
     arg2)))


(define (if-proc arg1)
  (make-proc
   (λ (arg2)
     (make-proc
      (λ (arg3)
        (let ([condition (resolve-closure arg1)])
          (when (not (int? condition)) (error "condition invalid"))
          (if (= (cadr condition) 0) arg3 arg2)))))))



(define (eval-proc foo args)
  (when (not (proc? foo)) (error "not a proc"))
  ((cadr foo) args))

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



(define (compile-ctor Tname CTname CTargs stack)
  (if (null? CTargs)
      (list 'cval Tname CTname
            (list 'λ 'f (list* 'f stack)))
      (list 'λ (car CTargs)
            (compile-ctor Tname CTname (cdr CTargs)
                          (cons (car CTargs) stack)))))

(define (ctor-pred ctor ctenv)
  (make-proc
   (λ (tval tvenv)
     (let ([ctorkw  (extract-keyword ctor)]
           [tvalval (eval-force tval tvenv)])
       (when (not (typed-val? tvalval)) (error "not a typed value"))
       (if (eq? (caddr tvalval) ctorkw)
           (make-int 1)
           (make-int 0))))))

(define (val-func Rfunc funcenv)
  (make-proc
   (λ (Rval valenv)
     (let* ([tval (eval-force Rval)]
            [valf (cadddr tval)]
            [func Rfunc])                ; (eval-force Rfunc)
       (when (not (typed-val? tval)) (error "not a typed value"))
       (eval(make-appl func tval))))))

;; A type def looks like this, which is eqv to
;;   '(T t ([c1 a b]    <=>    data t = c1 a b
;;          [c2 c])                   | c2 c
;;     expr)                  expr with this type def
;;
;; '(T t ((c1 a b)) a) -> '((λ c1 a) (λ a (λ b (cval t c1 (λ f (f b a))))))
;;
(define (compile-type-def xs)
  (when (not (eq? (car xs) 'T)) (error "not a type definition"))
  (let ([Tname (cadr xs)]
        [ctors (caddr xs)]
        [expr  (cadddr xs)])
    (foldl (λ (ctor expr)
             (let ([CTname (car ctor)]
                   [CTargs (cdr ctor)])
               (list (list 'λ CTname expr)
                     (compile-ctor Tname CTname CTargs '()))))
           expr
           ctors)))

(define (compile-lambda xs)
  (when (not (eq? (car xs) 'λ)) (error "not a lambda"))
  (let ([args (cadr xs)]
        [body (compile (caddr xs))])
    (define (compile-lambda-dyarg xs)
      (if (null? xs)
          body
          (list 'λraw (car xs) (compile-lambda-dyarg (cdr xs)))))
    (if (pair? args)
        (compile-lambda-dyarg args)
        (list 'λraw args body))))


;; This function compiles '(+ 1 (+ 2 3)) into
;;   '(appl (appl (p +) (i 1)) (appl (appl (p +) (i 2)) (i 3)))
(define (compile a)
  (cond
   [(and (symbol? a)
         (proc-exists? a)) (list 'p (lookup-proc a))]
   [(symbol? a) (list 'r a)]
   [(number? a) (list 'i a)]
   [(pair? a) (case (car a)
                ['λ (compile-lambda a)]
                ['T (compile (compile-type-def a))]
                [else (compile-fold-appl a)])]))


(define proc-map
  `([+     ,plus]
    [die   ,die]
    [trace ,trace]
    [if    ,if-proc]
    [cval  ,cval-proc]
    [ctorp ,ctor-pred]
    [fval  ,val-func]
    ))




(display "---Test basic evaluation---\n")
(eval-force (compile
             '(+ 1 (+ 2 3)))
            '())
;; should get 6

(display "---Test lambda---\n")
(eval-force (compile
             '((λ (a b) (+ a b)) 1 2)
             )
            '())
;; should get 3


;; Test delay
(display "---Test delay---\n")
(eval-force (compile
             '((λ (a b) a) 1 s)
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


;; Test type definition compilation
(display "---Test definition---\n")
; (compile (compile-type-def '(T t ((c1 a b) (c2 a)) c1)))
(eval-force (compile '(T t ((c1 a b) (c2 a)) (c1 1 2)))
            empty-env)
;; This should output a structure typed 'V, which represents a typed value.
;; The output could be long and messy, but it should indicates out the type
;; and the constructor used for this value.


;; A trial on implementing
(display "---A very beautiful program---\n")
(define y-combinator
  (compile
   '(λ f (λ x f (x x)) (λ x f (x x)))))
(define recur-env (add-binding 'Y y-combinator empty-env))

;; fix (\f xs -> if (xs == []) then 0 else 1 + f (tail xs)) [1,2,3]  =>  3
(define prog '(T L ((Nil a) (Cons hd tl))
               ((λ (lst len) (len lst))
                (Cons 1 (Cons 2 (Cons 3 (Nil 999))))
                (Y (λ (len xs) (if (ctor-p Nil xs)
                                   0
                                   (+ 1 (len (fval (λ (hd tl) hd) xs)))))))))

(eval-force (compile prog)
            recur-env)
;; They were like my children that I can't adore more.
