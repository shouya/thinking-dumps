#lang racket

(require "huffman.rkt")

(define sample-tree
  (make-code-tree (make-leaf 'A 4)
                  (make-code-tree (make-leaf 'B 2)
                                  (make-code-tree (make-leaf 'C 1)
                                                  (make-leaf 'D 1)))))

(define sample-message '(0 1 1 0 0 1 0 1 0 1 1 1 0))

(println (decode sample-message sample-tree))
;; output: '(A C A B B D A)
