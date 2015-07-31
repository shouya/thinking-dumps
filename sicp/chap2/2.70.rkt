#lang racket

(require "huffman.rkt")
(require "2.68.rkt") ; encode
(require "2.69.rkt") ; generate-huffman-tree

(define symbol-pairs
  '([A 2]
    [NA 16]
    [BOOM 1]
    [SHA 3]
    [GET 2]
    [YIP 9]
    [JOB 2]
    [WAH 1]))

(define message
  (string-append "GET A JOB SHA NA NA NA NA NA NA NA NA "
                 "GET A JOB SHA NA NA NA NA NA NA NA NA "
                 "WAH YIP YIP YIP YIP YIP YIP YIP YIP YIP "
                 "SHA BOOM"))
(define symbol-list
  (map string->symbol (string-split (string-upcase message))))



(define tree (generate-huffman-tree symbol-pairs))

(define bits (encode symbol-list tree))

(println bits)
(println (decode bits tree))
(printf "it takes ~a bits using huffman tree\n" (length bits))
(printf "it takes ~a bits using fixed 8-bit ascii\n"
        (* 8 (string-length message)))
