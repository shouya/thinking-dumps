
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



;; New
(define (ver-dist-point p1 p2)
  (abs (- (y-point p1)
          (y-point p2))))
(define (hor-dist-point p1 p2)
  (abs (- (x-point p1)
          (x-point p2))))


;; Method 1 to define a rectangle
; (define (make-rect p1 p2)
;   (cons p1 p2))
; (define (start-rect rect) (car rect))
; (define (end-rect rect) (cdr rect))

;; Method 2
(define (make-rect p1 p2)
  (list (x-point p1)
        (x-point p2)
        (y-point p1)
        (y-point p2)))
(define (start-rect rect)
  (make-point (car rect)
              (caddr rect)))
(define (end-rect rect)
  (make-point (cadr rect)
              (cadddr rect)))



(define (height-rect rect)
  (ver-dist-point (start-rect rect)
                  (end-rect rect)))
(define (width-rect rect)
  (hor-dist-point (start-rect rect)
                  (end-rect rect)))


(define (circum-rect rect)
  (* 2 (+ (height-rect rect)
          (width-rect rect))))
(define (area-rect rect)
  (* (height-rect rect)
     (width-rect rect)))

;; Abstract Layers:
;;
;; 1. cons / list / car / cdr / cadr ...
;; 2. make-rect / start-rect / end-rect
;; 3. width-rect / height-rect
;; 4. circum-rect / area-rect
;;


(let ((rect (make-rect (make-point 1 2)
                       (make-point 3 4))))
  (display (area-rect rect))     ;=> 4
  (newline)
  (display (circum-rect rect))   ;=> 8
  (newline))

