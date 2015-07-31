#lang racket

(require "huffman.rkt")

(define (encode message tree)
  (if (null? message) '()
      (append (encode-symbol (car message) tree)
              (encode (cdr message) tree))))

(define (encode-symbol sym tree)
  (cond [(and (leaf? tree) (eq? sym (symbol-leaf tree))) '()]
        [(in-set? sym (symbols (left-branch tree)))
         (cons 0 (encode-symbol sym (left-branch tree)))]
        [(in-set? sym (symbols (right-branch tree)))
         (cons 1 (encode-symbol sym (right-branch tree)))]
        [else (error "unknown symbol " sym)]))


;; sample data
(define sample-tree
  (make-code-tree (make-leaf 'A 4)
                  (make-code-tree (make-leaf 'B 2)
                                  (make-code-tree (make-leaf 'C 1)
                                                  (make-leaf 'D 1)))))

(println (encode '(A B C D) sample-tree))
