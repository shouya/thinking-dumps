
(define (mul-interval x y)
  (let ((p1 (* (lower-bound x) (lower-bound y)))
        (p2 (* (lower-bound x) (upper-bound y)))
        (p3 (* (upper-bound x) (lower-bound y)))
        (p4 (* (upper-bound x) (upper-bound y))))
    (make-interval (min p1 p2 p3 p4)
                   (max p1 p2 p3 p4))))

(define make-interval cons)

;; exercise 2.7
(define lower-bound car)
(define upper-bound cdr)

(define (add-interval x y)
  (make-interval (+ (lower-bound x) (lower-bound y))
                 (+ (upper-bound x) (upper-bound y))))

;; exercise 2.8
(define (sub-interval x y)
  (make-interval (- (lower-bound x) (upper-bound y))
                 (- (upper-bound x) (lower-bound y))))


;; exercise 2.10
(define (div-interval x y)
  (if (and (< (lower-bound y) 0)
           (> (upper-bound y) 0))
      (begin
        (display "error: divisor interval spans across the zero point")
        (newline)
        (exit))
      (mul-interval x
                    (make-interval (/ 1.0 (upper-bound y))
                                   (/ 1.0 (lower-bound y))))))
;; test case
(if #t
    (let ((intv1 (make-interval 2 5))
          (intv2 (make-interval -3 -1))
          (intv3 (make-interval -3 2)))
      (div-interval intv1 intv2)
      (div-interval intv1 intv3))
    '())

;; exercise 2.12
(define (make-center-percent c p)
  (make-interval (- c (* c p))
                 (+ c (* c p))))
(define (percent i)
  (/ (- (upper-bound i) (lower-bound i))
     (+ (upper-bound i) (lower-bound i))))
