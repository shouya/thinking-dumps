;; not solved
(define (reverse sequence)
  (fold-right (lambda (x y) (cons ) '() sequence))

; done
(define (reverse sequence)
  (fold-left (lambda (x y) (cons y x)) '() sequence))

