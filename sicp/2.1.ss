


(define (add-rat x y)
  (make-rat (+ (* (numer x) (denom y))
               (* (numer y) (denom x)))
            (* (denom x) (denom y))))

(define (sub-rat x y)
  (make-rat (- (* (numer x) (denom y))
               (* (numer y) (denom x)))
            (* (denom x) (denom y))))

(define (mul-rat x y)
  (make-rat (* (numer x) (numer y))
            (* (denom x) (denom y))))

(define (div-rat x y)
  (make-rat (* (numer x) (denom y))
            (* (numer y) (denom x))))

; (define (make-rat n d) (cons n d))
; (define (make-rat n d)
;   (let ((g (gcd n d)))
;     (cons (/ n g)
;           (/ d g))))


(define (make-rat n d)
  (let* ((xor (lambda (x y)
                (or (and x (not y))
                    (and y (not x)))))
         (neg? (xor (negative? n)
                    (negative? d)))
         (abs-n (abs n))
         (abs-d (abs d))
         (g (gcd abs-n abs-d))
         (new-n (/ abs-n g))
         (new-d (/ abs-d g))
         (signed-n (if neg? (- new-n) new-n)))
    (cons signed-n new-d)))

(define (neg-rat x)
  (make-rat (- (numer x))
            (denom x)))



(define (numer x) (car x))
(define (denom x) (cdr x))


(define (print-rat x)
  (display (numer x))
  (display "/")
  (display (denom x))
  (newline))

(define one-half (make-rat 1 2))
(define one-third (make-rat 1 3))


(print-rat (add-rat one-half one-third))
(print-rat (add-rat one-third one-third))
(print-rat (add-rat (neg-rat one-half)
                    one-third))
(print-rat (mul-rat (neg-rat one-third)
                    (neg-rat one-third)))


