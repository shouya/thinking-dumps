

(define (install-rational-package)
  (define (make-rational p1 p2) (list p1 p2))
  (define divident car)
  (define divisor cadr)

  (define (add-rational r1 r2)
    (let ([a (divident r1)]
          [b (divisor r1)]
          [c (divident r2)]
          [d (divisor r2)])
      (make-rational (add (mult a d) (mult b c))
                     (mult b d))))

  (put 'add '(rational rational) add-rational)

  'done)
