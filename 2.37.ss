(define (accumulate op initial sequence)
  (if (null? sequence)
      initial
      (op (car sequence)
          (accumulate op initial (cdr sequence)))))

; Dot product
(define (dot-product v w)
  (accumulate + 0 (map * v w)))

; Matrix * Vector
; http://upload.wikimedia.org/math/d/c/f/dcf8ccf9344226b39a18818eb03eea6e.png
(define (matrix-*-vector m v)
  (map (lambda (w) (map * w v)) m))

; Matrix * Matrix
; http://upload.wikimedia.org/math/7/b/c/7bc5e0122746b494cc5844db44ef975c.png
; http://upload.wikimedia.org/math/7/b/6/7b62cda9a2e78e8414806c5aea486b5c.png
; http://upload.wikimedia.org/math/d/3/c/d3c223ed4af4939e565893b2f3136bae.png
;; NOT BEST SOLUTION
(define (matrix-*-matrix m n)
  (map (lambda (mi)
         (accumulate-n + 0
                       (map (lambda (mii ni)
                              (map * ni (map (lambda _ mii) ni)))
                            mi n)))
       m))


; Transpose
(define (accumulate-n op init seqs)
  (if (null? (car seqs)) '()
      (cons (accumulate op init (map car seqs) )
            (accumulate-n op init (map cdr seqs)))))

(define (transpose mat)
  (accumulate-n cons '() mat))
