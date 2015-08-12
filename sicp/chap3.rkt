#lang racket

;; ex 3.1 make an accumulator
(define (make-accumulator n)
  (define x n)
  (λ (amount)
    (begin (set! x (+ x amount))
           x)))

;; ex 3.2 make function monitor wrapper
(define (make-monitored func)
  (define call-count 0)
  (λ xs (if (and (not (null? xs))
                 (= (length xs) 1)
                 (eq? 'how-many-calls? (car xs)))
            call-count
            (apply func xs))))


;; ex 3.3 account with password
#;
(define (make-account balance password)
  (define (withdraw amount)
    (if (>= balance amount)
        (set! balance (- balance amount))
        (error "insufficient balance")))
  (define (deposit amount)
    (set! balance (+ balance amount)))

  (define (password-correct? pwd) (eq? pwd password))

  (λ (password op)
    (if (password-correct? password)
        (cond [(eq? op 'withdraw) withdraw]
              [(eq? op 'deposit)  deposit])
        (error "wrong password!"))))


;; ex 3.4
(define (make-account balance password)
  (define (withdraw amount)
    (if (>= balance amount)
        (set! balance (- balance amount))
        (error "insufficient balance")))
  (define (deposit amount)
    (set! balance (+ balance amount)))
  (define mistake-count 0)

  (define (password-correct? pwd) (eq? pwd password))

  (λ (password op)
    (if (password-correct? password)
        (begin
          (set! mistake-count 0)
          (cond [(eq? op 'withdraw) withdraw]
                [(eq? op 'deposit)  deposit]))
        (begin
          (set! mistake-count (+ mistake-count 1))
          (if (> mistake-count 7)
              (error "☎︎110") ; or call-the-cops
              (error "wrong password!"))))))


;; ex 3.5 monte carlo integration
(define (monte-carlo trials experiment)
  (define (iter trials-remaining trials-passed)
    (cond ((= trials-remaining 0)
           (/ trials-passed trials))
          ((experiment)
           (iter (- trials-remaining 1) (+ trials-passed 1)))
          (else
           (iter (- trials-remaining 1) trials-passed))))
  (iter trials 0))

(define (random-in-range low high)
  (let ((range (- high low)))
    (+ low (* (random) range))))

(define (estimate-integral p x1 x2 y1 y2 trials)
  (define (new-p)
    (let ([x (random-in-range x1 x2)]
          [y (random-in-range y1 y2)])
      (p x y)))
  (monte-carlo trials new-p))

(define (estimated-pi radius trials)
  (define (in-circle? x y)
    (< (+ (expt x 2) (expt y 2))
       (expt radius 2)))

  (define ratio (estimate-integral in-circle?
                                   (- radius) radius
                                   (- radius) radius
                                   trials))
  ;; ratio = (pi * r^2) / (4 * r^2), pi = ratio * 4
  (exact->inexact (* ratio 4)))


;; ex 3.6 random with reset func
(define (make-rand seed)
  (define (rand op)
    (define (reset new-seed)
      (set! seed new-seed))
    (define (generate)
      ;; from microsoft random algorithm
      (set! seed (remainder (+ (* 214013 seed) 2531011) (expt 2 31)))
      seed)

    (cond [(eq? op 'reset) reset]
          [(eq? op 'generate) (generate)]))
  rand)


;; ex 3.7 make joint account
(define (make-joint-account acc password specific-password)
  (define (password-correct? pwd) (eq? pwd specific-password))
  (define (operate pwd operation)
    (if (password-correct? pwd)
        (acc password operation)
        (error "wrong password!")))
  operate)

;; ex 3.8 detect eval
(define (define-detector)
  (define val '())
  (define (func v)
    (if (null? val)
        (begin (set! val v) v)
        v))
  func)
(define f (define-detector))

;; f remember the first arg it was called with
;; and ignores those in all other calls


;; 3.9 show call tree

;; for clarity, i will use infix/s-expr mixed style

;; rec ver:
;;   (factorial 6)
;;   6 * (factorial 5)
;;   6 * 5 * (factorial 4)
;;   6 * 5 * 4 * (factorial 3)
;;   6 * 5 * 4 * 3 * (factorial 2)
;;   6 * 5 * 4 * 3 * 2 * (factorial 1)
;;   6 * 5 * 4 * 3 * 2 * 1
;;   6 * 5 * 4 * 3 * 2
;;   6 * 5 * 4 * 6
;;   6 * 5 * 24
;;   6 * 120
;;   720

;; iter ver:
;;   (factorial 6)
;;   (fact-iter 1 1 6)
;;   (fact-iter (1 * 1) (1 + 1) 6)
;;   (fact-iter (2 * 1) (2 + 1) 6)
;;   (fact-iter (3 * 2) (3 + 1) 6)
;;   (fact-iter (6 * 4) (4 + 1) 6)
;;   (fact-iter (24 * 5) (5 + 1) 6)
;;   (fact-iter (120 * 6) (6 + 1) 6)
;;   (fact-iter 720 7 6)
;;   720


;; ex 3.10 show expansion for the two defns of make-withdraw

;;    (let ((balance initial-amount)) ...)
;; => ((λ (balance) ...) initial-amount)
;;
;; which is just the same as using balance directly in
;;
;;    (define (make-withdraw balance) ...)
;;
;; the only difference is that the latter one adds a new layer
;; in the lookup stack, but it doesn't really matter.



;; ex 3.11 show env model for make-account

;; so I can use strings instead of comments with italic font
;; to draw the diagram
(define (comment x) (values))

(comment "
   +---------------------------------------+
   | <global env>               acc        |
   +-----------------------------+---------+
        ^                        |
        |                        |
   +----------------+            |
   | balance        | (make-acc) |
   +----------------+            |
      ^         ^                | (dispatching)
      |         |                |
   +-------------------+         |
   | withdraw, deposit |<--------+
   +-------------------+ "
         )



;;;;;;;; CHAPTER 3.3 MODELING WITH MUTABLE DATA ;;;;;;;

(require compatibility/mlist)
(require racket/mpair)

;; ex 3.12 trace the behavior of append vs append!

;; (define x (list 'a 'b))
;; (define y (list 'c 'd))
;; (define z (append x y))
;; z
;; => (a b c d)
;; (cdr x)
;; => (b)
;; (define w (append! x y))
;; w
;; => (a b c d)
;; (cdr x)
;; => (b c d)


;; ex 3.13 describe a looping pair

;; x:
;; a --> b --> c --> '()
;;
;; (make-cycle x):
;; a --> b --> c --+
;; ^               |
;; +---------------+
;;

;; ex 3.14 describe the function of mystery

;; it reverses a list, destructively
;;
;; v: '(a)
;; w: '(d c b a)


;; ex 3.15 describe the effect of set-wow! on z1 and z2
;;
;; z1: (cons '(wow b) '(wow b))
;; z2: (cons '(wow b) '(a b))


;; ex 3.16 trick count-pairs to return wrong results
(define (count-pairs x)
  (if (not (mpair? x))
      0
      (+ (count-pairs (mcar x))
         (count-pairs (mcdr x))
         1)))

(define ret-3 (mcons 1 (mcons 2 (mcons 3 '()))))
(define ret-4
  (let* ([tail (mcons 3 '())]
         [x (mcons tail tail)]
         [y (mcons 1 x)])
    y))
(define ret-7
  (let* ([tail (mcons 3 '())]
         [x (mcons tail tail)]
         [y (mcons x x)])
    y))
(define ret-inf
  (let* ([tail (mcons 3 '())]
         [x (mcons tail tail)]
         [y (mcons x x)])
    (set-mcar! tail tail)
    y))

;; ex 3.17 implement a correct count-pairs
;;

(define (count-pairs-1 x)
  (define (aux x visited)
    (if (not (mpair? x))
        0
        (if (memq x visited)
            0
            (+ 1
               (aux (mcdr x) (cons (mcar x) (cons x visited)))
               (aux (mcar x) (cons x visited))))))
  (aux x '()))


;; ex 3.18 detect infinite list

(define (detect x)
  (define (aux x visited)
    (if (not (mpair? x))
        'no
        (if (memq x visited)
            'yes
            (aux (mcdr x) (cons x visited)))))
  (aux x '()))


;; ex 3.19 detect infinite list with O(1) space

(define (detect-O1 x)
  (define (aux x y)
    (if (or (not (mpair? x))
            (not (mpair? y))
            (not (mpair? (mcdr y))))
        'no
        (if (eq? x y)
            'yes
            (aux (cdr x) (cdr (cdr y))))))
  (aux x x))


;; ex 3.20 illustrate this set-car!
(comment
 "
  +---+---+
  | o | o | z
  +-|-+-|-+
    |   |
    v   v
  +---+---+
  | 1 | 2 | x
  +---+---+

becomes:

  +---+---+
  | o | o | z
  +-|-+-|-+
    |   |
    v   v
  +----+---+
  | 17 | 2 | x
  +----+---+
")


;; queue:

(define (front-queue queue)
  (if (empty-queue? queue)
      (error "FRONT called with an empty queue" queue)
      (mcar (front-ptr queue))))
(define (make-queue) (mcons '() '()))

(define (empty-queue? queue) (null? (front-ptr queue)))

(define (front-ptr queue) (mcar queue))
(define (rear-ptr queue) (mcdr queue))
(define (set-front-ptr! queue item) (set-mcar! queue item))
(define (set-rear-ptr! queue item) (set-mcdr! queue item))



(define (delete-queue! queue)
  (cond ((empty-queue? queue)
         (error "DELETE! called with an empty queue" queue))
        (else
         (set-front-ptr! queue (mcdr (front-ptr queue)))
         queue)))

(define (insert-queue! queue item)
  (let ((new-pair (mcons item '())))
    (cond ((empty-queue? queue)
           (set-front-ptr! queue new-pair)
           (set-rear-ptr! queue new-pair)
           queue)
          (else
           (set-mcdr! (rear-ptr queue) new-pair)
           (set-rear-ptr! queue new-pair)
           queue))))


;; ex 3.21 correctly print an queue

(define (print-queue queue)
  (print (reverse (mlist->list (mcar queue)))))


;; ex 3.22 implement queue in the dispatcher way

(define (make-queue-proc)
  (let ([front-ptr '()]
        [rear-ptr '()])
    (define (enqueue e)
      (let ([cns (mcons e '())])
        (if (null? front-ptr)
            (begin
              (set! front-ptr cns)
              (set! rear-ptr cns))
            (begin
              (set-mcdr! rear-ptr cns)
              (set! rear-ptr cns))
            )))
    (define (dequeue)
      (if (null? front-ptr)
          (error "empty queue")
          (let ([elm (mcar front-ptr)])
            (set! front-ptr (mcdr front-ptr))
            elm)
          ))
    (define (show)
      (println (mlist->list front-ptr)))

    (define (dispatch m)
      (cond [(eq? 'enq  m) enqueue]
            [(eq? 'deq  m) dequeue]
            [(eq? 'show m) show]
            ))

    dispatch))


;; ex 3.23 implmenent deque

(define (make-deque)
  (define front-ptr '())
  (define rear-ptr '())

  (define (push e)
    (define new-node (mcons e (mcons '() front-ptr)))
    (if (null? front-ptr)
        (begin
          (set! front-ptr new-node)
          (set! rear-ptr  new-node))
        (begin
          (set-mcar! (mcdr front-ptr) new-node)
          (set! front-ptr new-node)))
    'ok)
  (define (pop)
    (if (null? front-ptr)
        (error "null front-ptr")
        (let ([e (mcar front-ptr)])
          (set! front-ptr (mcdr (mcdr front-ptr)))
          (if (null? front-ptr)
              (set! rear-ptr '())
              (set-mcar! (mcdr front-ptr) '()))
          e)))

  (define (unshift e)
    (define new-node (mcons e (mcons rear-ptr '())))
    (println rear-ptr)
    (if (null? rear-ptr)
        (begin
          (set! front-ptr new-node)
          (set! rear-ptr new-node))
        (begin
          (set-mcdr! (mcdr rear-ptr) new-node)
          (set! rear-ptr new-node)))
    'ok)

  (define (shift)
    (if (null? rear-ptr)
        (error "rear ptr is null")
        (let ([e (mcar rear-ptr)])
          (set! rear-ptr (mcar (mcdr rear-ptr)))
          (if (null? rear-ptr)
              (set! front-ptr '())
              (set-mcdr! (mcdr rear-ptr) '()))
          e
          )))

  (define (show)
    (define (show-iter node xs)
      (if (null? node)
          xs
          (show-iter (mcdr (mcdr node))
                     (cons (mcar node) xs))))
    (show-iter front-ptr '()))

  (define (dispatch m . args)
    (cond [(eq? 'push    m) (apply push args)]
          [(eq? 'pop     m) (pop)]
          [(eq? 'unshift m) (apply unshift args)]
          [(eq? 'shift   m) (shift)]
          [(eq? 'show    m) (show)]
          [else (error "unknown method")]))

  dispatch)


;; 3.24 implement table in a closure

(define (make-table same-key?)
  (define table (mlist 'table))

  (define (inspect) table)

  (define (assoc k lst)
    (if (null? lst)
        #f
        (if (same-key? k (mcar (mcar lst)))
            (mcar lst)
            (assoc k (mcdr lst)))))

  (define (lookup k1 k2)
    (define row (assoc k1 (mcdr table)))
    (if (not row)
        (error "k1 not found")
        '())

    (define col (assoc k2 (mcdr row)))
    (if (not col)
        (error "k2 not found")
        '())
    (mcdr col))

  (define (add! key val lst)
    (set-mcdr! lst (mcons (mcons key val) (mcdr lst))))

  (define (insert! k1 k2 val)
    (define subtable (assoc k1 (mcdr table)))
    (if subtable
        (let ([record (assoc k2 (mcdr subtable))])
          (if record
              (set-mcdr! record val)
              (add! k2 val subtable)))
        (add! k1 (mlist (mcons k2 val)) table)))

  (define (dispatch m . as)
    (apply (cond [(eq? m 'insert!) insert!]
                 [(eq? m 'lookup ) lookup]
                 [(eq? m 'inspect) inspect]
                 ) as))
  dispatch)


;; ex 3.25 generalize table to have various number of keys

(define (make-generalized-table same-key?)
  (define table (mlist 'table))

  (define (inspect) table)

  (define (assoc k lst)
    (if (null? lst)
        #f
        (if (same-key? k (mcar (mcar lst)))
            (mcar lst)
            (assoc k (mcdr lst)))))

  (define (lookup keys)
    (define (iter keys table)
      ((if (null? keys)
           (mcdr table)
           (let ([result (assoc (car keys) (mcdr table))])
             (if (not result)
                 (error "not found")
                 (iter (cdr keys) result))))))
    (iter keys table))

  (define (add! keys val table)
    (define (sub keys)
      (if (null? keys)
          val
          (mcons (car keys) (sub (cdr keys)))))
    (set-mcdr! table (cons (sub keys) (mcdr table))))

  (define (insert! keys val)
    (println keys val table)
    (define (iter keys table)
      (if (null? keys)
          (set-mcdr! table val)
          (let ([subtable (assoc (car keys) (mcdr table))])
            (if subtable
                (iter (cdr keys) subtable)
                (add! keys val subtable)))))
    (iter keys table))


  (define (dispatch m . as)
    (apply (cond [(eq? m 'insert!) insert!]
                 [(eq? m 'lookup ) lookup]
                 [(eq? m 'inspect) inspect])
           as))
  dispatch)
