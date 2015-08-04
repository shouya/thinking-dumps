
(define (install-subtraction-package)
  ;; for demo, i only implement subtraction for complex number.
  ;; rational and scheme number should be implemented as well
  ;; in real case.
  ;;

  ;; c1 - c2
  (define (complex-subt c1 c2)
    (let ([c1a (real-part c1)]
          [c2a (real-part c2)]
          [c1b (imag-part c1)]
          [c2b (imag-part c2)])
      (make-from-real-imag (- c1a c2a)
                           (- c1b c2b))))

  (put 'subtract '(complex complex) complex-subt)
  'done)

(define (install-polynomial-subtraction-package)
  (define (poly-subt p1 p2)
    (define var (variable p1))
    (define neg1 (make var '((-1 0))))
    (add p1 (mul p2 neg1)))

  (put 'subtract '(polynomial polynomial) poly-subt)
  'done)
