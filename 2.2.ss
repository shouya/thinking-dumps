
(define (print-point p)
  (display "(")
  (display (x-point p))
  (display ",")
  (display (y-point p))
  (display ")"))


(define (print-point-newline p)
  (print-point p)
  (newline))

; Have fun :)
(define (make-point x y)
  (lambda (q) (if q x y)))
(define (x-point p) (p #t))
(define (y-point p) (p #f))

(define (make-segment p1 p2)
  (cons p1 p2))
(define (start-segment seg) (car seg))
(define (end-segment seg) (cdr seg))

(define (midpoint-segment seg)
  (make-point (/ (+ (x-point (start-segment seg))
                    (x-point (end-segment seg))) 2)
              (/ (+ (y-point (start-segment seg))
                    (y-point (end-segment seg))) 2)))


(define (print-segment seg)
  (print-point (start-segment seg))
  (display "-")
  (print-point (end-segment seg)))
(define (print-segment-newline seg)
  (print-segment seg)
  (newline))


; Test cases
(let ((seg (make-segment (make-point 1 2)
                         (make-point 3 4))))
  (print-segment-newline seg)
  (print-point-newline (midpoint-segment seg)))

