;;
;; not easy huh?
;;
;; let's try!

(define (make-poly term-list) term-list)
(define (first-term poly) (car poly))
(define (rest-terms poly) (cdr poly))
(define empty-termlist? null?)
(define the-empty-termlist '())

(define (make-term coeff var-ords) (list coeff var-ords))
(define coeff car)
(define var-ords cadr)

(define (make-simple-term var order) (list var order))
(define var car)
(define order cadr)

(define (prod-terms t1 t2)
  (define (adjoin-prod vo vos)
    (if (null? vos)
        (list vo)
        (if (eq? (var vo) (var (car vos)))
            (cons (make-simple-term (var vo)
                                    (+ (order vo) (order (car vos))))
                  (cdr vos))
            (cons (car vos) (adjoin-prod vo (cdr vos))))))

  (define (merge-var-ords vos)
    (if (null? vos)
        '()
        (adjoin-prod (car vos)
                     (merge-var-ords (cdr vos)))))

  (make-term (* (coeff t1) (coeff t2))
             (merge-var-ords (append t1 t2))))



(define (adjoin-term term poly)
  (if (empty-termlist? poly)
      (list term)
      (if (equal? (term-signature term) (term-signature (first-term poly)))
          (cons (make-term (+ (coeff term) (coeff (first-term poly)))
                           (var-ords term))
                (rest-terms poly))
          (cons (first-term poly) (adjoin-term term (rest-terms poly))))))

(define (term-signature t)
  (let ([t-ordered (sort string<? #:key var)])
    (list (coef))))



;; ORDER BY `order` DESC XD
;;

(define (add p1 p2)
  (if (null? p1) p2
      (adjoin-term (car p1) (add (cdr p1) p2))))

(define (mul p1 p2)
  (if (or (null? p1) (null? p2)) (the-empty-termlist)
      (mult-one-term (car p1)
                             (mul (cdr p1) p2))))

(define (mult-one-term t p)
  (map (λ (x) (prod-terms t x)) p))
