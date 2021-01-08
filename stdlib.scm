(define map
  (let ((null? null?)
	(car car) (cdr cdr)
	(cons cons) (apply apply))
  (letrec ((map-many
	    (lambda (f lists)
	      (if (null? (car lists))
		  '()
		  (cons
		   (apply f (map-one car lists))
		   (map-many f (map-one cdr lists))))))
	   (map-one
	    (lambda (f s)
	      (if (null? s)
		  '()
		  (cons (f (car s))
			(map-one f (cdr s)))))))
    (lambda (f . args)
      (map-many f args)))))


(define fold-left (lambda (op base lst) (if (null? lst) base (fold-left op (op base (car lst)) (cdr lst)))))


(let ((flonum? flonum?) (rational? rational?)
      (exact->inexact exact->inexact)
      (fold-left fold-left) (map map)
      (_+ +) (_* *) (_/ /) (_= =) (_< <)
      (car car) (cdr cdr) (null? null?))
  (let ((^numeric-op-dispatcher
	 (lambda (op)
	   (lambda (x y)
	     (cond
	      ((and (flonum? x) (rational? y)) (op x (exact->inexact y)))
	      ((and (rational? x) (flonum? y)) (op (exact->inexact x) y))
	      (else (op x y)))))))
    (let ((^comparator
	  (lambda (op)
	    (lambda (x . ys)
	      (fold-left (lambda (a b) (and a b)) #t
			 (map (lambda (y) (op x y)) ys))))))
      (set! = (^comparator (^numeric-op-dispatcher _=))))))
