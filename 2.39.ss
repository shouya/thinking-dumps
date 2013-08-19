(define (accumulate op initial sequence)
  (if (null? sequence)
      initial
      (op (car sequence)
          (accumulate op initial (cdr sequence)))))
(define fold-right accumulate)

;; done
(define (reverser sequence)
  (fold-right (lambda (x y) (append y (list x))) '() sequence))

; done
(define (reversel sequence)
  (fold-left (lambda (x y) (cons y x)) '() sequence))

(display (reverser '(1 2 3 4)))
(newline)
