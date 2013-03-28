(define-syntax dmatch
  (syntax-rules ()
    ((_ v (e ...) ...)
     (let ((pkg* (dmatch-remexp v (e ...) ...)))
       (run-a-thunk 'v v #f pkg*)))
    ((_ v name (e ...) ...)
     (let ((pkg* (dmatch-remexp v (e ...) ...)))
       (run-a-thunk 'v v 'name pkg*)))))

(define pkg (lambda (cls thk) (cons cls thk)))
(define pkg-clause (lambda (pkg) (car pkg)))
(define pkg-thunk (lambda (pkg) (cdr pkg)))

(define-syntax dmatch-remexp
  (syntax-rules ()
    ((_ (rator rand ...) cls ...)
     (let ((v (rator rand ...)))
       (dmatch-aux v cls ...)))
    ((_ v cls ...) (dmatch-aux v cls ...))))

(define-syntax dmatch-aux
  (syntax-rules (guard)
    ((_ v) '())
    ((_ v (pat (guard g ...) e0 e ...) cs ...)
     (let ((fk (lambda () (dmatch-aux v cs ...))))
       (ppat v pat
         (if (not (and g ...))
           (fk)
           (cons (pkg '(pat (guard g ...) e0 e ...) 
	              (lambda () e0 e ...)) 
             (fk)))
         (fk))))
    ((_ v (pat e0 e ...) cs ...)
     (let ((fk (lambda () (dmatch-aux v cs ...))))
       (ppat v pat
         (cons (pkg '(pat e0 e ...)
                    (lambda () e0 e ...)) 
	       (fk))
         (fk))))))

(define-syntax ppat
  (syntax-rules (unquote)
    ((_ v (unquote var) kt kf) (let ((var v)) kt))
    ((_ v (x . y) kt kf)
     (if (pair? v)
       (let ((vx (car v)) (vy (cdr v)))
         (ppat vx x (ppat vy y kt kf) kf))
       kf))
    ((_ v lit kt kf) (if (equal? v (quote lit)) kt kf))))

(define run-a-thunk 
  (lambda (v-expr v name pkg*)
    (cond
      ((null? pkg*)
       (no-matching-pattern name v-expr v))
      ((null? (cdr pkg*))
       ((pkg-thunk (car pkg*))))
      (else 
       (overlapping-patterns/guards name v-expr v pkg*)))))

(define no-matching-pattern
  (lambda (name v-expr v)
    (if name
      (printf "dmatch ~d failed~n~d ~d~n"
              name v-expr v)
      (printf "dmatch failed~n~d ~d~n"
              v-expr v))
    (error 'dmatch "match failed")))

(define overlapping-patterns/guards
  (lambda (name v-expr v pkg*)
    (if name
      (printf "dmatch ~d overlapping matching clauses~n"
              name)
      (printf "dmatch overlapping matching clauses~n"))
    (printf "with ~d evaluating to ~d~n" v-expr v)
    (printf "____________________________________~n")    
    (for-each pretty-print (map pkg-clause pkg*))
    (error 'dmatch "")))
