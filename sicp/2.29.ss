
(define (make-mobile left right)
  (list left right))

(define (make-branch len struct)
  (list len struct))



; (define (cadr x) (car (cdr x)))

;; Question a)
(define left-branch car)
(define right-branch cadr)
(define branch-length car)
(define branch-structure cadr)
(define mobile? list?)



;; Question b)
(define (total-weight struct)
  (if (not (mobile? struct)) struct
      (+ (total-weight (branch-structure (left-branch struct)))
         (total-weight (branch-structure (right-branch struct))))))
(if #t
    (begin
      (display "testing `total-weight`") (newline)
    '()
))


;; Question c)
(define (equilibrium? struct)
  (if (not (mobile? struct)) #t
      (let ((left (left-branch struct))
            (right (right-branch struct)))
        (and (equilibrium? (branch-structure left))
             (equilibrium? (branch-structure right))
             (= (* (branch-length left)
                   (total-weight (branch-structure left)))
                (* (branch-length right)
                   (total-weight (branch-structure right))))))))

(if #t
    (let ((eq-branch (make-mobile
                       (make-branch 10 11)
                       (make-branch 10
                                    (make-mobile (make-branch 1 10)
                                                 (make-branch 10 1)))))
          (diseq-branch (make-mobile
                          (make-branch 10 20)
                          (make-branch 10
                                       (make-mobile (make-branch 1 10)
                                                    (make-branch 10 10))))))
      (display "testing `equilibrium?`") (newline)

      (display (equilibrium? eq-branch))
      (newline)
      (display (equilibrium? diseq-branch))
      (newline))
    '()
)


;; Question d)
;(if #f
;    (begin
;      (define make-mobile cons)
;      (define left-branch car)
;      (define right-branch cdr)
;      (define make-branch cons)
;      (define branch-length car)
;      (define branch-structure cdr)
;      (define mobile? pair?)
;      ) '())
