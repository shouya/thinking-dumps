(require "alg.rkt")

;;
;; 這題好 testicle painful...
;;

;; 我都不想做了（
;;

(define (install-poly-poly-term-format-package)
  (define (adjoin-term-sparse term term-list)
    (if (=zero? (coeff term))
        term-list
        (cons term term-list)))

  (define (the-empty-termlist) '())
  (define (first-term-sparse term-list) (car term-list))
  (define (rest-terms term-list) (cdr term-list))
  (define (empty-termlist? term-list) (null? term-list))
  (define (make-term order coeff) (list order coeff))
  (define (order term) (car term))
  (define (coeff term) (cadr term))

  (define tag cons)

  (put 'adjoin-term '(term sparse-term-list)
       (λ (a b) (tag 'sparse-term-list (adjoin-term-sparse a b))))
  (put 'the-empty-termlist 'sparse-term-list
       (λ () (tag 'sparse-term-list (the-empty-termlist))))
  (put 'first-term '(sparse-term-list)
       (λ (x) (tag 'term (first-term-sparse x))))
  (put 'rest-terms '(sparse-term-list)
       (λ (x) (tag 'sparse-term-list (rest-terms x))))
  (put 'empty-termlist? '(sparse-term-list)
       (λ (x) (tag 'bool (empty-termlist? x))))
  (put 'make-term '(scheme-number complex)
       (λ (a b) (tag 'term (make-term a b))))
  (put 'order '(term) (λ (x) (tag 'scheme-number (order x))))
  (put 'coeff '(term) (λ (x) (tag 'complex-number (coeff x))))

  (define (adjoin-term-dense term term-list)
    (if (=zero? (order term))
        (cons (coeff term) term-list)
        (cons (car term-list)
              (adjoin-term-dense (make-term (- (order term) 1)
                                            (coeff term))
                                 (cdr term-list)))))
  (define (first-term-dense term-list)
    (make-term (- (length term-list) 1)
               (car term-list)))

  (put 'adjoin-term '(term dense-term-list)
       (λ (a b) (tag 'dense-term-list (adjoin-term-dense a b))))
  (put 'the-empty-termlist 'dense-term-list
       (λ () (tag 'dense-term-list (the-empty-termlist))))
  (put 'first-term '(dense-term-list)
       (λ (x) (tag 'term (first-term-dense x))))
  (put 'rest-terms '(dense-term-list)
       (λ (x) (tag 'dense-term-list (rest-terms x))))
  (put 'empty-termlist? '(dense-term-list)
       (λ (x) (tag 'bool (empty-termlist? x))))
  )
