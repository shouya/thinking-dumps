;;
;; not runnable
;;

(define (union-set set1 set2)
  ;; merge for merge in mergesort
  (list->tree (merge (tree->list-1 set1)
                     (tree->list-2 set2))))


(define (intersect l1 l2)
  (if (or (null? l1) (null? l2)) '()
      (cond ([(= (car l1) (car l2))
              (cons (car l1) (intersect (cdr l1) (cdr l2)))]
             [(< (car l1) (car l2))
              (intersect (cdr l1) l2)]
             [(> (car l1) (car l2))
              (intersect l1 (cdr l2))]))))

(define (intersection-set set1 set2)
  (list->tree (intersect (tree->list-1 set1)
                         (tree->list-2 set2))))
