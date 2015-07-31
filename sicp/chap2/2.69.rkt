#lang racket

(require "huffman.rkt")

(define (generate-huffman-tree pairs)
  (successive-merge (make-leaf-set pairs)))

(define (successive-merge set)
  (match set
    [(list a b rest ...)
     (let* ([tree (make-code-tree a b)]
            [new-set (adjoin-set tree rest)])
       (successive-merge new-set))]
    [(list a) a])) ; stop at singleton


;;; test
(define leaf-pairs '([A 4] [B 2] [C 1] [D 1]))
(println (show-tree (generate-huffman-tree leaf-pairs)))
