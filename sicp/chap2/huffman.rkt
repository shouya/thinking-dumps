#lang racket

(require racket/match)

(provide (all-defined-out))

;; representation

(define (make-leaf symbol weight)
  (list 'leaf symbol weight))
(define (leaf? obj)
  (eq? (car obj) 'leaf))
(define (symbol-leaf x) (cadr x))
(define (weight-leaf x) (caddr x))


(define (make-code-tree left right)
  (list left
        right
        (append (symbols left) (symbols right))
        (+ (weight left) (weight right))))


(define (left-branch x) (car x))
(define (right-branch x) (cadr x))
(define (symbols tree)
  (if (leaf? tree) (list (symbol-leaf tree))
      (caddr tree)))
(define (weight tree)
  (if (leaf? tree) (weight-leaf tree)
      (cadddr tree)))



;; decoding
(define (decode bits tree)
  (define (decode-1 bits current-branch)
    (if (null? bits) '()
        (let ([next-branch (choose-branch (car bits) current-branch)])
          (if (leaf? next-branch)
              (cons (symbol-leaf next-branch)
                    (decode-1 (cdr bits) tree))
              (decode-1 (cdr bits) next-branch)))))
  (decode-1 bits tree))

(define (choose-branch bit branch)
  (cond [(= bit 0) (left-branch branch)]
        [(= bit 1) (right-branch branch)]
        [else (error "bad bit " bit)]))


;; weighted set as an ordered list
(define (adjoin-set x set)
  (cond [(null? set) (list x)]
        [(< (weight x) (weight (car set))) (cons x set)]
        [else (cons (car set) (adjoin-set x (cdr set)))]))


(define (make-leaf-set pairs)
  (match pairs
    ['() '()]
    [(cons (list sym freq) ps)
     (adjoin-set (make-leaf sym freq)
                 (make-leaf-set ps))]))


(define (in-set? x set) (memq x set))

(define (show-tree tree)
  (if (leaf? tree) (symbol-leaf tree)
      (list (show-tree (left-branch tree))
            (show-tree (right-branch tree)))))
