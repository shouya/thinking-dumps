
(define (last-pair lst)
  (cond
   ((null? lst) "failed")
   ((null? (cdr lst)) lst)
   (else (last-pair (cdr lst)))))

(display (last-pair '(23 72 149 34)))
(newline)
