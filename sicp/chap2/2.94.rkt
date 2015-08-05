
(define (remainder-terms a b) (cadr (div-terms a b)))

(define (gcd-terms a b)
  (if (empty-termlist? b)
      a
      (gcd-terms b (remainder-terms a b))))
