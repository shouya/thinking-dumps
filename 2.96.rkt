(define (integerize p q)
  (pow (coeff (first-term q))
       (+ 1 (- (order (first-term p))
               (order (first-term q))))))

(define (pseudo-remainder-terms a b)
  (div-terms (mult (integerize a b) a)
             b))
