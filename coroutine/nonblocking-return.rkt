#lang racket

(define queue '())
(define (enqueue! task)
  (set! queue (append queue (list task))))
(define (dequeue!)
  (let ((head (car queue)))
    (set! queue (cdr queue))
    head))

(define halt (lambda () (println "not running yet")))

(define curr-task 'main)
(define tasks (make-hash))
(define (task-cont task)
  (hash-ref tasks task))
(define (set-task-cont! task cont)
  (hash-set! tasks task cont))
(define (del-task! task)
  (hash-remove! tasks task))

(define return-values (make-hash))
(define (set-return-value! task val)
  (hash-set! return-values task val))
(define (task-returned? task)
  (hash-has-key? return-values task))
(define (pop-task-return-value! task)
  (let ((value (hash-ref return-values task)))
    (hash-remove! return-values task)
    value))

(define (run-next-task)
  (if (not (empty? queue))
      (begin
        (set! curr-task (dequeue!))
        ((task-cont curr-task) '()))
      (halt)))

(define (return-value val)
  (set-return-value! curr-task val))

(define (spawn f)
  (let* ((task (gensym))
         (cont (lambda (_)
                 (return-value (f))
                 (del-task! task)
                 (run-next-task))))
    (set-task-cont! task cont)
    (enqueue! task)
    task))

(define (yield)
  (call/cc
   (lambda (k)
     (set-task-cont! curr-task k)
     (enqueue! curr-task)
     (run-next-task))))

(define (run f)
  (call/cc
   (lambda (k)
     (set! halt (lambda () (k 'done)))
     (join f))))

(define (join task)
  (if (task-returned? task)
      (pop-task-return-value! task)
      (begin
        (yield)
        (join task))))

(define (sleep-until t)
  (when (< (current-milliseconds) t)
    (yield)
    (sleep-until t)))

(define (sleep ms)
  (sleep-until (+ ms (current-milliseconds))))

(define (select task-1 task-2)
  (if (task-returned? task-1)
      (pop-task-return-value! task-1)
      (if (task-returned? task-2)
          (pop-task-return-value! task-2)
          (begin
            (yield)
            (select task-1 task-2)))))

(define t1 (spawn (lambda () (println 1) (yield) (println 2)
                    (define t2 (spawn (lambda () (print 7) (yield))))
                    t2
                    )))
(define t3 (spawn (lambda () (println 3) (yield) (println 4) 3)))
(define t4 (spawn (lambda () (println 5) (yield) (println 6) 5)))

(define main (spawn (lambda ()
                      (join t4)
                      (sleep 1000)
                      (println "sleep")
                      (join t3)
                      (join (join t1))
                      )))
(run main)
