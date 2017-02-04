#lang racket

; (define (yield val)
;   (cont val (call/cc (λ (id) id))))

(define (create-coroutine f)
  (λ ()
    (let ([ret (call/cc (λ (return) (f return)))]
          [cont (car ret)]
          [val (cdr ret)])
      (


  (call/cc (λ (cont)
             (let ([yield (λ (val)
                            (cont val)
                            (create-coroutine))])
               yield))))

(define (foo v yield)
  (let ([new-yield (yield v)])
    (print v new-yield)
    (foo (- v 1) new-yield)))
