#lang racket

(define entry car)
(define left-branch cadr)
(define right-branch caddr)
(define (make-tree ent l r) (list ent l r))

(define (list->tree elms)
  (car (partial-tree elms (length elms))))

(define (partial-tree elts n)
  (if (= n 0) (cons '() elts)
      (let* ([left-size (quotient (- n 1) 2)]
             [left-result (partial-tree elts left-size)]
             [left-tree (car left-result)]
             [non-left-elts (cdr left-result)]
             [right-size (- n (+ left-size 1))]
             [this-entry (car non-left-elts)]
             [right-result (partial-tree (cdr non-left-elts)
                                         right-size)]
             [right-tree (car right-result)]
             [remaining-elts (cdr right-result)])
        (cons (make-tree this-entry left-tree right-tree)
              remaining-elts))))

;; a) explain how partial-tree works
;;
;; it's a recursive algorithm. it takes a list of elements
;; and return a pair by the created tree and a list of
;; remaining elements. the algorithm first generate the
;; left subtree and use the rest to generate the right
;; subtree (yeah and the current entry). finally it combines
;; the results (left/right subtree, current entry) into a tree.
;; the terminal condition is simple, it just returns the
;; empty tree when the size of tree it need to construct is 0.
;;
;;
;; b) what's the time complexity of this algorithm?
;;
;; aha, it's O(N).
;;
