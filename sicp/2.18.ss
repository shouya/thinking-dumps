
(define (reverse lst)
  (define (reverse-helper a b)
    (if (null? a) b
        (reverse-helper (cdr a)
                        (cons (car a) b))))
  (reverse-helper lst '()))

(define (reverse2 lst)
  (define (reverse-helper a)
    (if (null? (cdr a)) (list (car a))
        (append (reverse-helper (cdr a))
                (list (car a)))))
  (reverse-helper lst))


(display (reverse '(1 2 3 4)))
(newline)
(display (reverse2 '(1 2 3 4)))
(newline)

