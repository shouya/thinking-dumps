

(define (map-tree proc tree)
  (if (not (pair? tree)) (proc tree)
      (map (lambda (ele) (map-tree proc ele))
           tree)))

(define (map-tree2 proc tree)
  (cond ((null? tree) '())
        ((not (pair? tree)) (proc tree))
        (else (cons (map-tree2 proc (car tree))
                    (map-tree2 proc (cdr tree))))))

(define (scale-tree tree scl)
  (map-tree (lambda (x) (* x scl)) tree))
(define (square-tree tree)
  (map-tree2 (lambda (x) (* x x)) tree))


(display (scale-tree '(1 2 3 (4 5 (6 7 8))) 2))
(newline)
(display (square-tree '(1 2 3 (4 5 (6 7 8)))))
(newline)

