(define (gcd-mult xs)
  (if (= 0 (length xs))
      (car xs)
      (gcd (car xs) (gcd-mult (cdr xs)))))


(define (reduce-terms n d)
  (define gcd1 (gcd n d))
  (define int (integerize n d))
  (define n1 (div-terms (mult int n) gcd1))
  (define d1 (div-terms (mult int d) gcd1))

  (define n-gcd (gcd-mult (map coeff n1)))
  (define d-gcd (gcd-mult (map coeff d1)))

  (define n2 (div n1 n-gcd))
  (define d2 (div d1 d-gcd))

  (make-rational n2 d2))
