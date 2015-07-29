#lang racket

(define entry car)
(define left-branch cadr)
(define right-branch caddr)
(define (make-tree ent l r) (list ent l r))

(define (element-of-set? x set)
  (cond [(null? set) #f]
        [(= x (entry set)) #t]
        [(< x (entry set))
         (element-of-set? x (left-branch set))]
        [(> x (entry set))
         (element-of-set? x (right-branch set))]
        ))

(define (adjoin-set x set)
  (cond [(null? set) (list x)]
        [(= x (entry set)) set]
        [(< x (entry set))
         (make-tree (entry set)
                    (adjoin-set x (left-branch set))
                    (right-branch set))]
        [(> x (entry set))
         (make-tree (entry set)
                    (left-branch set)
                    (adjoin-set x (right-branch set)))]
        ))


(define (tree->list-1 tree)
  (if (null? tree) '()
      (append (tree->list-1 (left-branch tree))
              (cons (entry tree)
                    (tree->list-1 (right-branch tree))))))

(define (tree->list-2 tree)
  (define (copy-to-list tree result)
    (if (null? tree) result
        (copy-to-list (left-branch tree)
                      (cons (entry tree)
                            (copy-to-list (right-branch tree) result)))
        )))

;; a) do these two procedures the produce the same
;;    result for the same input?
;;
;; answer: no. it depends on the evaluation order of params
;;         the first uses typical recursion while the second
;;         uses tail recursion.

;; b) does these two func has same time complexity for a
;;    balanced tree?
;;
;; answer: they are different. the second is linear growth
