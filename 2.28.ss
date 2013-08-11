
(define (fringe lst)
  (fold-left (lambda (a b)
               (let ((rhs (if (list? b)
                              (fringe b)
                              (list b))))
                 (append a rhs)))
             '() lst))

(display (fringe '((1 2) (3 4 (3)))))
(newline)


