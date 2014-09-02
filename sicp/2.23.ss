
(define (my-for-each proc lst)
  (map proc lst)
  '())

(define (my-for-each2 proc lst)
  (if (null? lst) '()
      (begin
        (proc (car lst))
        (my-for-each2 proc (cdr lst)))))
