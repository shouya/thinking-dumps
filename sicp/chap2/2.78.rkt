
(define (attach-tag tag value)
  (if (eq? tag 'number)
      value
      (cons tag value)))

(define (type-tag datum)
  (if (number? datum) 'number
      (car datum)))

(define (contents datum)
  (if (number? datum) datum
      (cdr datum)))
