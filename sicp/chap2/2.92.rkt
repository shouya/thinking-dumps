;;
;; not easy huh?
;;
;; let's try!

(define (make-term var order coeff) (list var order coeff))
(define var   car)
(define order cadr)
(define coeff caddr)

(define (make-poly term-list) term-list)
(define (first-term poly) (car poly))
(define (rest-terms poly) (cdr poly))

(define empty-termlist? null?)


;; ORDER BY `order` DESC XD
;;
(define (adjoin-term t p)
  (if (null? p)
      (make-poly (list t))
      (cond [(and (eq? (var t) (var (first-term p)))
                  (= (order t) (order (first-term p))))
             (cons (make-term (var t)
                              (order t)
                              (+ (coeff t) (coeff (first-term p))))
                   (rest-terms p))]
            [(>= (order t) (order (first-term p)))
             (cons t (cons (first-term p) (rest-terms p)))]
            [(< (order t) (order (first-term p)))
             (cons (first-term p) (adjoin-term t (rest-terms p)))])))


(define (add p1 p2)
  (cond [(empty-termlist? p1) p2]
        [(empty-termlist? p2) p1]
        [else (adjoin-term (car p1))
              (add (cdr p1) p2)]))
