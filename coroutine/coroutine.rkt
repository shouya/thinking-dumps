#lang racket

(define curr-task-handle 'main)
(define queue '())
(define joiners '())

(define (enqueue task)
  (set! queue (append queue (list task))))
(define (dequeue)
  (let ((head (car queue))
        (tail (cdr queue)))
    (set! queue tail)
    head))

(define (make-task handle cont)
  (cons handle cont))
(define (task-handle task) (car task))
(define (task-cont task) (cdr task))

(define (make-joiner handle cont)
  (cons handle cont))
(define (joiner-handle task) (car task))
(define (joiner-cont task) (cdr task))

(define (register-joiner joiner)
  (set! joiners (cons joiner joiners)))
(define (pop-joiner handle)
  (let ((joiner (assoc handle joiners))
        (updated-joiners (filter (lambda (j) (not (eq? (joiner-handle j) handle))) joiners)))
    (set! joiners updated-joiners)
    joiner))

(define (return-val handle retval)
  (let ((joiner (pop-joiner handle)))
    (cond
      ((eq? joiner #f)
       ;; joiner not found, I'll wait here until someone joins me
       (yield)
       (return-val handle retval))
      (#t ((joiner-cont joiner) retval)))))

(define (yield)
  (call/cc
   (lambda (new-cont)
     (enqueue (make-task curr-task-handle new-cont))
     (run-next-task))))

(define (spawn fn)
  (let* ((handle (gensym))
         (cont (lambda (_any)
                 (return-val handle (fn))))
         (task (make-task handle cont)))
    (enqueue task)
    handle))

(define (join handle)
  (call/cc (lambda (cont)
             (register-joiner (make-joiner handle cont))
             (run-tasks)
             )))

(define (select h1 h2)
  (let ((retval (call/cc (lambda (cont)
                           (register-joiner (make-joiner h1 cont))
                           (register-joiner (make-joiner h2 cont))
                           (run-tasks)))))
    (cleanup-tasks (list h1 h2))
    retval))

(define (cleanup-tasks handles)
  (set! queue (filter (lambda (t) (not (member (task-handle t) handles)))
                      queue)))

(define (run-next-task)
  (let* ((next-task (dequeue))
         (next-task-cont (task-cont next-task))
         (next-task-handle (task-handle next-task)))
    (set! curr-task-handle next-task-handle)
    (next-task-cont '())))

(define (run-tasks)
  (when (not (empty? queue))
    (run-next-task)
    (run-tasks)))

(define (sleep-until t)
  (when (< (current-milliseconds) t)
    (yield)
    (sleep-until t)))

(define (sleep n)
  (sleep-until (+ (current-milliseconds) n)))

(select (spawn (lambda () (sleep 100) 1))
        (spawn (lambda () (sleep 200) 2))
        )

(let* ((N 10)
       (task (lambda (i) (sleep 100) (* i 2)))
       (tasks (map (lambda (i) (spawn (lambda () (task i))))
                   (range 0 N)))
       (retvals (map (lambda (handle) (join handle)) tasks)))
  retvals)

(println (length queue))

;
;(define t1 (spawn (lambda ()
;                    (sleep 1000)
;                    (print "task 1")
;                    "task 1 ret")))
;(define t2 (spawn (lambda ()
;                    (sleep 2000)
;                    (print "task 2")
;                    "task 2 ret")))

;; (print queue)

;; (join t2 3000)
;; (print "aaaaa")
;; (join t1 3000)
