(define (element-of-set? x set)
  (cond [(null? set) #f]
        [(= x (car set)) #t]
        [(< x (car set)) #f]
        [else
         (element-of-set? x (cdr set))]))

(define (intersection set1 set2)
  (cond [(or (null? set1) (null? set2)) '()]
        [(= (car set1) (car set2))
         (cons (car set1) (intersection (cdr set1) (cdr set2)))]
        [(< (car set1) (car set2))
         (intersection (cdr set1) set2)]
        [else
         (intersection set1 (cdr set2))]))

;; this is the same as the merge step in a mergesort
(define (union-set set1 set2)
  (cond [(null? set1) set2]
        [(null? set2) set1]
        [(= (car set1) (car set2))
         (cons (car set1) (union-set (cdr set1) (cdr set2)))]
        [(< (car set1) (car set2))
         (cons (car set1) (union-set (cdr set1) set2))]
        [(> (car set1) (car set2))
         (cons (car set2) (union-set set1 (cdr set2)))]))
