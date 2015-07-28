
(define (same-parity . x)
  (define (same-parity-helper p b)
    (cond
     ((null? b) '())
     (p    (cons (car b)
                 (same-parity-helper (not p) (cdr b))))
     (else (same-parity-helper (not p) (cdr b)))))
  (same-parity-helper #t x))

(display (same-parity 1 2 3 4 5 6 7))
(newline)




