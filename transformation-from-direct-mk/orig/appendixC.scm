(load "testcheck.scm")
(load "replacestar.scm")

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


(define h
  (lambda (x y)
    (dmatch `(,x . ,y) "example"
      ((,a . ,b)
       (guard (number? a) (number? b))
       (* a b))
      ((,a ,b ,c)
       (guard (number? a) (number? b) (number? c))
       (+ a b c)))))

(test-check "appC-1"
  (list (h 3 4) (apply h `(1 (3 4))))
  '(12 8))

(print-gensym #f)
(test-check "appC-2"
  (call-with-string-output-port
   (lambda (p) (display
           (expand
            '(lambda (x y)
               (dmatch `(,x . ,y) "example"
                       ((,a . ,b)
                        (guard (number? a) (number? b))
                        (* a b)))))
           p)))
  (call-with-string-output-port
   (lambda (p) (display
           (replace-respect-quote*
            '((cons . #2%cons)
              (pair? . #2%pair?)
              (car . #2%car)
              (cdr . #2%cdr)
              (not . #2%not)
              (number? . #2%number?)
              (* . #2%*))
            '(lambda (x y)
               (let ((pkg*
                      (let ((v (cons x y)))
                        (let ((fk (lambda () '())))
                          (if (pair? v)
                              (let ((vx (car v)) (vy (cdr v)))
                                (let ((a vx))
                                  (let ((b vy))
                                    (if (not (if (number? a) (number? b) #f))
                                        (fk)
                                        (cons
                                         (pkg
                                          '((,a . ,b)
                                            (guard
                                             (number? a)
                                             (number? b))
                                            (* a b))
                                          (lambda () (* a b)))
                                         (fk))))))
                              (fk))))))
                 (run-a-thunk '`(,x . ,y) (cons x y) "example" pkg*))))
           p))))
