(require "alg.rkt")

(define (div-terms L1 L2)
  (if (empty-termlist? L1)
      (list (the-empty-termlist) (the-empty-termlist))
      (let ((t1 (first-term L1))
            (t2 (first-term L2)))
        (if (> (order t2) (order t1))
            (list (the-empty-termlist) L1)
            (let ((new-c (div (coeff t1) (coeff t2)))
                  (new-o (- (order t1) (order t2))))
              (let* ([rest-of-poly
                      ;; <compute rest of result recursively>
                      (subtract L1
                                (mul L2 (adjoin-term (make-term new-o new-c)
                                                     (the-empty-termlist))))]
                     [rest-of-result (div-terms rest-of-poly L2)])
                (list (adjoin-term (make-term new-o new-c)
                                   (car rest-of-result))
                      (cadr rest-of-result))
                ))))))
