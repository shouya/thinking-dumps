
(define (reverse lst)
  (define (reverse-helper a b)
    (if (null? a) b
        (reverse-helper (cdr a)
                        (cons (car a) b))))
  (reverse-helper lst '()))

(define (deep-reverse lst)
  (map (lambda (e)
         (if (list? e)
             (deep-reverse e) e))
       (reverse lst)))

(display (reverse '((1 2) (3 4))))
(newline)
(display (deep-reverse '((1 2) (3 4))))
(newline)

