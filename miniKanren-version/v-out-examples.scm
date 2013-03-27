#!/usr/bin/env scheme-script
(import (rnrs) (mk-lib) (test-check-lib))

;;; examples of the v-out technique

;;; punchline for rembero examples:
;;;
;;; CPSing rembero causes this test to diverge:
;;;
;;;  (test "rembero-8"
;;;    (run* (q)
;;;      (fresh (rest-a rest-b)
;;;        (rembero 'y `(x . ,rest-a) `(z . ,rest-b))))
;;;    '())
;;;
;;; v-out allows this test to fail finitely once again.  Seems like
;;; CPS + v-out results in same divergence behavior as direct style.
;;; Is there a way to prove this?

(let ()

  (define rember
    (lambda (x ls)
      (cond
        [(null? ls) '()]
        [(eq? x (car ls)) (rember x (cdr ls))]
        [else
         (cons (car ls) (rember x (cdr ls)))])))

  (printf "*** vanilla direct-style Scheme rember\n")
  
  (test "rember-1"
    (rember 'y '(x y z y w y y v))
    '(x z w v))

  )

(let ()
  
  (define rembero
    (lambda (x ls out)
      (conde
        [(== '() ls) (== ls out)]
        [(fresh (d)
           (== `(,x . ,d) ls)
;;; interesting!  even though this rembero is in direct-style, this
;;; tail call delays association between out and the other arguments.
;;; This seems to be why it is so easy to make this program diverge
;;; with illegal inputs (for example, 'x' in the 'out' variable).
;;; 'x' in 'out' could be presented with absento, but absento won't help
;;; with cases like:
;;;
;;;  (test "rembero-6"
;;;    (run 1 (q)
;;;      (fresh (rest-a rest-b)
;;;        (rembero q `(x y . ,rest-a) `(x z w y . ,rest-b))))
;;;    '())
;;;
;;; Can we use v-out or something similar to reclaim the association
;;; with 'out'?  I'm doubtful, since in this case it seems like we
;;; must perform recursion to learn anything about 'out'.
           (rembero x d out))]
        [(fresh (a d res)
           (== `(,a . ,d) ls)
           (=/= a x)
           (== `(,a . ,res) out)
           (rembero x d res))])))

  (printf "*** vanilla direct-style rembero\n")
  
  (test "rembero-1"
    (run* (q)
      (rembero 'y '(x y z y w y y v) q))
    '((x z w v)))

  (test "rembero-2"
    (run* (q)
      (rembero q '(x y z y w y y v) '(x z w v)))
    '(y))

  (test "rembero-3"
    (run 5 (q)
      (rembero 'y q '(x z w v)))
    '((x z w v)
      (x z w v y)
      (x z w y v)
      (x z y w v)
      (x y z w v)))

  (test "rembero-4"
    (run 5 (q)
      (fresh (x ls out)
        (rembero x ls out)
        (== `(,x ,ls ,out) q)))
    '((_.0 () ())
      (_.0 (_.0) ())
      ((_.0 (_.1) (_.1)) (=/= ((_.0 _.1))))
      (_.0 (_.0 _.0) ())
      ((_.0 (_.1 _.0) (_.1)) (=/= ((_.0 _.1))))))

  (test "rembero-5"
    (run* (q)
      (rembero q '(x y) '(x z w y)))
    '())

;;; diverges  
;  (test "rembero-6"
;    (run 1 (q)
;      (fresh (rest-a rest-b)
;        (rembero q `(x y . ,rest-a) `(x z w y . ,rest-b))))
;    '())

;;; diverge  
  ;; (test "rembero-7a"
  ;;   (run 1 (q)
  ;;     (rembero 'x q '(x)))
  ;;   '())
  
  ;; (test "rembero-7b"
  ;;   (run* (q)
  ;;     (rembero 'x q '(x z w y)))
  ;;   '())

  (test "rembero-8"
    (run* (q)
      (fresh (rest-a rest-b)
        (rembero 'y `(x . ,rest-a) `(z . ,rest-b))))
    '())
  
  )

(let ()
;;; Doesn't seem to be any point to v-out in direct-style--just
;;; mirrors behavior of 'out'.
  
  (define rembero-aux
    (lambda (x ls out v-out)
      (conde
        [(== '() ls) (== ls out) (== ls v-out)]
        [(fresh (d)
           (== `(,x . ,d) ls)
           (rembero-aux x d out v-out))]
        [(fresh (a d res v-out-res)
           (== `(,a . ,d) ls)
           (=/= a x)
           (== `(,a . ,res) out)
           (== `(,a . ,v-out-res) v-out)
           (rembero-aux x d res v-out-res))])))

  (define rembero
    (lambda (x ls out)
      (fresh (v-out)
        (== out v-out)
        (rembero-aux x ls out v-out))))

;;; direct style rembero, just for testing
  (define direct-rembero
    (lambda (x ls out)
      (conde
        [(== '() ls) (== ls out)]
        [(fresh (d)
           (== `(,x . ,d) ls)
           (direct-rembero x d out))]
        [(fresh (a d res)
           (== `(,a . ,d) ls)
           (=/= a x)
           (== `(,a . ,res) out)
           (direct-rembero x d res))])))
  
  (printf "*** direct-style rembero with v-out\n")
  
  (test "rembero-1"
    (run* (q)
      (rembero 'y '(x y z y w y y v) q))
    '((x z w v)))

  (test "rembero-2"
    (run* (q)
      (rembero q '(x y z y w y y v) '(x z w v)))
    '(y))

  (test "rembero-3"
    (run 5 (q)
      (rembero 'y q '(x z w v)))
    '((x z w v)
      (x z w v y)
      (x z w y v)
      (x z y w v)
      (x y z w v)))

  (test "rembero-4"
    (run 5 (q)
      (fresh (x ls out)
        (rembero x ls out)
        (== `(,x ,ls ,out) q)))
    '((_.0 () ())
      (_.0 (_.0) ())
      ((_.0 (_.1) (_.1)) (=/= ((_.0 _.1))))
      (_.0 (_.0 _.0) ())
      ((_.0 (_.1 _.0) (_.1)) (=/= ((_.0 _.1))))))

  (test "rembero-5"
    (run* (q)
      (rembero q '(x y) '(x z w y)))
    '())
  
 (test "rembero-b"
   (length
    (run 1000 (q)
      (fresh (x ls out)
        (== `(,x ,ls ,out) q)      
        (direct-rembero x ls out)
        (condu
          [(rembero x ls out)]
          [(errorg 'rembero-b "rembero can't handle state generated by direct-rembero:\n\n~s\n\n" q)]))))
   1000)

 (test "rembero-c"
   (length
    (run 1000 (q)
      (fresh (x ls out)
        (== `(,x ,ls ,out) q)      
        (rembero x ls out)
        (condu
          [(direct-rembero x ls out)]
          [(errorg 'rembero-c "direct-rembero can't handle state generated by rembero:\n\n~s\n\n" q)]))))
   1000)

;;; diverges  
;  (test "rembero-6"
;    (run 1 (q)
;      (fresh (rest-a rest-b)
;        (rembero q `(x y . ,rest-a) `(x z w y . ,rest-b))))
;    '())

;;; diverge  
  ;; (test "rembero-7a"
  ;;   (run 1 (q)
  ;;     (rembero 'x q '(x)))
  ;;   '())
  
  ;; (test "rembero-7b"
  ;;   (run* (q)
  ;;     (rembero 'x q '(x z w y)))
  ;;   '())

  (test "rembero-8"
    (run* (q)
      (fresh (rest-a rest-b)
        (rembero 'y `(x . ,rest-a) `(z . ,rest-b))))
    '())
  
  )

(let ()
  
  (define rember-cps
    (lambda (x ls k)
      (cond
        [(null? ls) (k '())]
        [(eq? x (car ls)) (rember-cps x (cdr ls) k)]
        [else
         (rember-cps x (cdr ls)
                     (lambda (v)
                       (k (cons (car ls) v))))])))

  (define rember
    (lambda (x ls)
      (rember-cps x ls (lambda (x) x))))
  
  (printf "*** CPS Scheme rember w/higher-order continuations\n")
  
  (test "rember-1"
    (rember 'y '(x y z y w y y v))
    '(x z w v))

  )

(let ()

  (define empty-k (lambda (x) x))

  (define rember-k
    (lambda (ls k)
      (lambda (v)
        (apply-k k (cons (car ls) v)))))
  
  (define apply-k
    (lambda (k v)
      (k v)))
  
  (define rember-cps
    (lambda (x ls k)
      (cond
        [(null? ls) (apply-k k '())]
        [(eq? x (car ls)) (rember-cps x (cdr ls) k)]
        [else (rember-cps x (cdr ls) (rember-k ls k))])))

  (define rember
    (lambda (x ls)
      (rember-cps x ls empty-k)))
  
  (printf "*** CPS Scheme rember w/higher-order (RI) continuations\n")
  
  (test "rember-1"
    (rember 'y '(x y z y w y y v))
    '(x z w v))

  )

(let ()

  (define empty-k 'empty-k)

  (define rember-k
    (lambda (ls k)
      `(rember-k ,ls ,k)))
  
  (define apply-k
    (lambda (k^ v)
      (cond
        [(eq? empty-k k^) v]
        [(eq? (car k^) 'rember-k)
         (let ([ls (cadr k^)]
               [k (caddr k^)])
           (apply-k k (cons (car ls) v)))])))

  (define rember-cps
    (lambda (x ls k)
      (cond
        [(null? ls) (apply-k k '())]
        [(eq? x (car ls)) (rember-cps x (cdr ls) k)]
        [else (rember-cps x (cdr ls) (rember-k ls k))])))

  (define rember
    (lambda (x ls)
      (rember-cps x ls empty-k)))
  
  (printf "*** CPS Scheme rember w/data-structural continuations\n")
  
  (test "rember-1"
    (rember 'y '(x y z y w y y v))
    '(x z w v))

  )

(let ()

  (define empty-k 'empty-k)

  (define rember-k
    (lambda (ls k)
      `(rember-k ,ls ,k)))
  
  (define apply-ko
    (lambda (k^ v out)
      (conde
        [(== empty-k k^) (== v out)]
        [(fresh (ls k a d)
           (== `(rember-k ,ls ,k) k^)
           (== `(,a . ,d) ls)
           (apply-ko k `(,a . ,v) out))])))

  (define rember-cpso
    (lambda (x ls k out)
      (conde
        [(== '() ls) (apply-ko k '() out)]
        [(fresh (d)
           (== `(,x . ,d) ls)
           (rember-cpso x d k out))]
        [(fresh (a d)
           (== `(,a . ,d) ls)
           (=/= x a)
           (rember-cpso x d (rember-k ls k) out))])))

  (define rembero
    (lambda (x ls out)
      (rember-cpso x ls empty-k out)))
  
  (printf "*** vanilla CPS rembero\n")
  
  (test "rembero-1"
    (run* (q)
      (rembero 'y '(x y z y w y y v) q))
    '((x z w v)))

  (test "rembero-2"
    (run* (q)
      (rembero q '(x y z y w y y v) '(x z w v)))
    '(y))

  (test "rembero-3"
    (run 5 (q)
      (rembero 'y q '(x z w v)))
    '((x z w v)
      (y x z w v)
      (x y z w v)
      (x z y w v)
      (x z w y v)))

  (test "rembero-4"
    (run 5 (q)
      (fresh (x ls out)
        (rembero x ls out)
        (== `(,x ,ls ,out) q)))
    '((_.0 () ())
      (_.0 (_.0) ())
      ((_.0 (_.1) (_.1)) (=/= ((_.0 _.1))))
      (_.0 (_.0 _.0) ())
      ((_.0 (_.0 _.1) (_.1)) (=/= ((_.0 _.1))))))

  (test "rembero-5"
    (run* (q)
      (rembero q '(x y) '(x z w y)))
    '())

;;; still diverges  (no surprise)
;  (test "rembero-6"
;    (run 1 (q)
;      (fresh (rest-a rest-b)
;        (rembero q `(x y . ,rest-a) `(x z w y . ,rest-b))))
;    '())

;;; diverge  
  ;; (test "rembero-7a"
  ;;   (run 1 (q)
  ;;     (rembero 'x q '(x)))
  ;;   '())
  
  ;; (test "rembero-7b"
  ;;   (run* (q)
  ;;     (rembero 'x q '(x z w y)))
  ;;   '())

;;; diverges due to CPS!!!!  
;  (test "rembero-8"
;    (run* (q)
;      (fresh (rest-a rest-b)
;        (rembero 'y `(x . ,rest-a) `(z . ,rest-b))))
;    '())
  
  )

(let ()

  (define empty-k 'empty-k)

  (define rember-k
    (lambda (ls k)
      `(rember-k ,ls ,k)))
  
  (define apply-ko
    (lambda (k^ v out)
      (conde
        [(== empty-k k^) (== v out)]
        [(fresh (ls k a d)
           (== `(rember-k ,ls ,k) k^)
           (== `(,a . ,d) ls)
           (apply-ko k `(,a . ,v) out))])))

  (define rember-cpso
    (lambda (x ls k out v-out)
      (conde
        [(== '() ls)
         (== '() v-out)
         (apply-ko k '() out)]
        [(fresh (d v-out-d)
           (== `(,x . ,d) ls)
           (rember-cpso x d k out v-out))]
        [(fresh (a d v-out-d)
           (== `(,a . ,d) ls)
           (=/= x a)
           (== `(,a . ,v-out-d) v-out)
;;; interesting: not necessary to put v-out in the continuation.  This
;;; differs from 'list' in the interpreter, since we don't have to
;;; evaluate 'a'. (In the interpreter, the first thing in the list is
;;; an expression, not a value.)
;;;
;;; Would be nice to have a slightly more complex example that
;;; required placing a v-out-related variable into the continuation.
           (rember-cpso x d (rember-k ls k) out v-out-d))])))

  (define rembero
    (lambda (x ls out)
      (fresh (v-out)
        (== out v-out)
        (rember-cpso x ls empty-k out v-out))))


;;; direct style rembero, just for testing
  (define direct-rembero
    (lambda (x ls out)
      (conde
        [(== '() ls) (== ls out)]
        [(fresh (d)
           (== `(,x . ,d) ls)
           (direct-rembero x d out))]
        [(fresh (a d res)
           (== `(,a . ,d) ls)
           (=/= a x)
           (== `(,a . ,res) out)
           (direct-rembero x d res))])))
  
  (printf "*** CPS rembero with v-out\n")

  (test "rembero-1"
    (run* (q)
      (rembero 'y '(x y z y w y y v) q))
    '((x z w v)))

  (test "rembero-2"
    (run* (q)
      (rembero q '(x y z y w y y v) '(x z w v)))
    '(y))

  (test "rembero-3"
    (run 5 (q)
      (rembero 'y q '(x z w v)))
    '((x z w v)
      (x z w v y)
      (x z w y v)
      (x z y w v)
      (x y z w v)))

  (test "rembero-4"
    (run 5 (q)
      (fresh (x ls out)
        (rembero x ls out)
        (== `(,x ,ls ,out) q)))
    '((_.0 () ())
      (_.0 (_.0) ())
      ((_.0 (_.1) (_.1)) (=/= ((_.0 _.1))))
      (_.0 (_.0 _.0) ())
      ((_.0 (_.0 _.1) (_.1)) (=/= ((_.0 _.1))))))

  
 (test "rembero-b"
   (length
    (run 1000 (q)
      (fresh (x ls out)
        (== `(,x ,ls ,out) q)      
        (direct-rembero x ls out)
        (condu
          [(rembero x ls out)]
          [(errorg 'rembero-b "rembero can't handle state generated by direct-rembero:\n\n~s\n\n" q)]))))
   1000)

 (test "rembero-c"
   (length
    (run 1000 (q)
      (fresh (x ls out)
        (== `(,x ,ls ,out) q)      
        (rembero x ls out)
        (condu
          [(direct-rembero x ls out)]
          [(errorg 'rembero-c "direct-rembero can't handle state generated by rembero:\n\n~s\n\n" q)]))))
   1000)

  (test "rembero-5"
    (run* (q)
      (rembero q '(x y) '(x z w y)))
    '())

;;; still diverges  (no surprise)
;  (test "rembero-6"
;    (run 1 (q)
;      (fresh (rest-a rest-b)
;        (rembero q `(x y . ,rest-a) `(x z w y . ,rest-b))))
;    '())

;;; diverge  
  ;; (test "rembero-7a"
  ;;   (run 1 (q)
  ;;     (rembero 'x q '(x)))
  ;;   '())
  
  ;; (test "rembero-7b"
  ;;   (run* (q)
  ;;     (rembero 'x q '(x z w y)))
  ;;   '())

  (test "rembero-8"
    (run* (q)
      (fresh (rest-a rest-b)
        (rembero 'y `(x . ,rest-a) `(z . ,rest-b))))
    '())
  
  )

(let ()
  
  (define rembero-aux
    (lambda (x ls out)
      (conde
        [(== '() ls) (== ls out)]
        [(fresh (d)
           (== `(,x . ,d) ls)
           (conde
             [(absento x d)
              (== d out)]
             [(=/= d out)
              (rembero-aux x d out)]))]
        [(fresh (a d res)
           (== `(,a . ,d) ls)
           (=/= a x)
           (== `(,a . ,res) out)
           (conde
             [(absento x d)
              (== d res)]
             [(=/= d res)
              (rembero-aux x d res)]))])))

  (define rembero
    (lambda (x ls out)
      (fresh ()
        (absento x out)
        (rembero-aux x ls out))))
  
;;; direct style rembero, just for testing
  (define direct-rembero
    (lambda (x ls out)
      (conde
        [(== '() ls) (== ls out)]
        [(fresh (d)
           (== `(,x . ,d) ls)
           (direct-rembero x d out))]
        [(fresh (a d res)
           (== `(,a . ,d) ls)
           (=/= a x)
           (== `(,a . ,res) out)
           (direct-rembero x d res))])))
  
  (printf "*** vanilla direct-style rembero, but using absento\n")
  
  (test "rembero-1"
    (run* (q)
      (rembero 'y '(x y z y w y y v) q))
    '((x z w v)))

  (test "rembero-2"
    (run* (q)
      (rembero q '(x y z y w y y v) '(x z w v)))
    '(y))

  (test "rembero-3"
    (run 5 (q)
      (rembero 'y q '(x z w v)))
    '((y x z w v)
      (x z w v)
      (y y x z w v)
      (x y z w v)
      (y x y z w v)))

  (test "rembero-4"
    (run 5 (q)
      (fresh (x ls out)
        (rembero x ls out)
        (== `(,x ,ls ,out) q)))
    '(((_.0 () ()) (=/= ((_.0 ()))))
      ((_.0 (_.0 . _.1) _.1) (absento (_.0 _.1)))
      ((_.0 (_.1 . _.2) (_.1 . _.2)) (=/= ((_.0 (_.1 . _.2)))) (absento (_.0 _.1) (_.0 _.2)))
      ((_.0 (_.0 _.0 . _.1) _.1) (absento (_.0 _.1)))
      ((_.0 (_.1 _.0 . _.2) (_.1 . _.2)) (=/= ((_.0 (_.1 . _.2)))) (absento (_.0 _.1) (_.0 _.2)))))

  (test "rembero-5"
    (run* (q)
      (rembero q '(x y) '(x z w y)))
    '())

 (test "rembero-b"
   (length
    (run 1000 (q)
      (fresh (x ls out)
        (== `(,x ,ls ,out) q)      
        (direct-rembero x ls out)
        (condu
          [(rembero x ls out)]
          [(errorg 'rembero-b "rembero can't handle state generated by direct-rembero:\n\n~s\n\n" q)]))))
   1000)

 (test "rembero-c"
   (length
    (run 1000 (q)
      (fresh (x ls out)
        (== `(,x ,ls ,out) q)      
        (rembero x ls out)
        (condu
          [(direct-rembero x ls out)]
          [(errorg 'rembero-c "direct-rembero can't handle state generated by rembero:\n\n~s\n\n" q)]))))
   1000)
  
;;; this test diverges without the absento mojo
 (test "rembero-6"
   (run 1 (q)
     (fresh (rest-a rest-b)
       (rembero q `(x y . ,rest-a) `(x z w y . ,rest-b))))
   '())

;;; these tests diverge without the absento mojo
   (test "rembero-7a"
     (run 1 (q)
       (rembero 'x q '(x)))
     '())
  
   (test "rembero-7b"
     (run* (q)
       (rembero 'x q '(x z w y)))
     '())

  (test "rembero-8"
    (run* (q)
      (fresh (rest-a rest-b)
        (rembero 'y `(x . ,rest-a) `(z . ,rest-b))))
    '())

  )

(let ()

  (define rember*
    (lambda (x ls)
      (cond
        [(null? ls) '()]
        [(list? (car ls)) (cons (rember* x (car ls)) (rember* x (cdr ls)))]
        [(eq? (car ls) x) (rember* x (cdr ls))]
        [else
          (cons (car ls) (rember* x (cdr ls)))])))

  (printf "*** vanilla direct-style Scheme rember*\n")

  (test "rember*-1"
    (rember* 'y '((x) (y) z y (w y y) v))
    '((x) () z (w) v))
  )

(let ()

  (define rember*o
    (lambda (x ls out)
      (conde
        [(== '() ls) (== ls out)]
        [(fresh (a d ra rd a1 a*)
           (== `(,a . ,d) ls)
           (== `(,ra . ,rd) out)
           (== `(,a1 . ,a*) a)
           (rember*o x a ra)
           (rember*o x d rd))]
        [(fresh (d)
           (== `(,x . ,d) ls)
           (rember*o x d out))]
        [(fresh (a d rd)
           (== `(,a . ,d) ls)
           (== `(,a . ,rd) out)
           (conde
             [(symbolo a)]
             [(== '() a)])
           (=/= a x)
           (rember*o x d rd))])))

  (printf "*** vanilla direct-style rember*o\n")

  (test "rember*o-1"
    (run* (q)
      (rember*o 'y '((x) (y) z y (w y y) v) q))
    '(((x) () z (w) v)))

  (test "rembero-1"
    (run* (q)
      (rember*o 'y '(x y z y w y y v) q))
    '((x z w v)))

  (test "rembero-2"
    (run* (q)
      (rember*o q '(x y z y w y y v) '(x z w v)))
    '(y))

  (test "rember*o-3"
    (run 5 (q)
      (rember*o 'y q '(x z w v)))
    '((x z w v)
      (x z w v y)
      (x z w v y y)
      (x z w y v)
      (x z y w v)))

  (test "rember*o-4"
    (run 5 (q)
      (fresh (x ls out)
        (rember*o x ls out)
        (== `(,x ,ls ,out) q)))
    '((_.0 () ())
      (_.0 (_.0) ())
      ((_.0 (_.1) (_.1)) (=/= ((_.0 _.1))) (sym _.1))
      ((_.0 (()) (())) (=/= ((_.0 ()))))
      (_.0 ((_.0)) (()))))

  (test "rembero-5"
    (run* (q)
      (rember*o q '(x y) '(x z w y)))
    '())

;;; diverge
 (test-disable "rembero-6"
   (run 1 (q)
     (fresh (rest-a rest-b)
       (rember*o q `(x y . ,rest-a) `(x z w y . ,rest-b))))
   '())

;;; diverge
  (test-disable "rembero-7a"
    (run 1 (q)
      (rember*o 'x q '(x)))
    '())
;;; diverge
  (test-disable "rembero-7b"
    (run* (q)
      (rember*o 'x q '(x z w y)))
    '())

  (test "rembero-8"
    (run* (q)
      (fresh (rest-a rest-b)
        (rember*o 'y `(x . ,rest-a) `(z . ,rest-b))))
    '())

  )

(let ()

  (define rember*-cps
    (lambda (x ls k)
      (cond
        [(null? ls) (k '())]
        [(list? (car ls)) (rember*-cps x (car ls)
                            (lambda (ra)
                              (rember*-cps x (cdr ls)
                                (lambda (rd)
                                  (k (cons ra rd))))))]
        [(eq? (car ls) x) (rember*-cps x (cdr ls) k)]
        [else (rember*-cps x (cdr ls)
                (lambda (rd)
                  (k (cons (car ls) rd))))])))

  (define rember*
    (lambda (x ls)
      (rember*-cps x ls (lambda (x) x))))

  (printf "*** CPS Scheme rember* w/higher-order continuations\n")

  (test "rember*-1"
    (rember* 'y '((x) (y) z y (w y y) v))
    '((x) () z (w) v))
  )

(let ()

  (define empty-k 'empty-k)

  (define rember-list-car-outer-k
    (lambda (x ls k)
      `(rember-list-car-outer-k ,x ,ls ,k)))

  (define rember-list-car-inner-k
    (lambda (ra k)
      `(rember-list-car-inner-k ,ra ,k)))

  (define rember-else-k
    (lambda (ls k)
      `(rember-else-k ,ls ,k)))

  (define apply-k
    (lambda (k^ v)
      (cond
        [(eq? empty-k k^) v]
        [(eq? (car k^) 'rember-list-car-outer-k)
         (let ([x (cadr k^)]
               [ls (caddr k^)]
               [k (cadddr k^)])
           (rember*-cps x (cdr ls) (rember-list-car-inner-k v k)))]
        [(eq? (car k^) 'rember-list-car-inner-k)
         (let ([ra (cadr k^)]
               [k (caddr k^)])
           (apply-k k (cons ra v)))]
        [(eq? (car k^) 'rember-else-k)
         (let ([ls (cadr k^)]
               [k (caddr k^)])
           (apply-k k (cons (car ls) v)))])))

  (define rember*-cps
    (lambda (x ls k)
      (cond
        [(null? ls) (apply-k k '())]
        [(list? (car ls)) (rember*-cps x (car ls) (rember-list-car-outer-k x ls k))]
        [(eq? (car ls) x) (rember*-cps x (cdr ls) k)]
        [else (rember*-cps x (cdr ls) (rember-else-k ls k))])))

  (define rember*
    (lambda (x ls)
      (rember*-cps x ls empty-k)))

  (printf "*** CPS Scheme rember* w/data-structural continuations\n")

  (test "rember*-1"
    (rember* 'y '((x) (y) z y (w y y) v))
    '((x) () z (w) v))
  )

(let ()

  (define empty-k 'empty-k)

  (define rember-list-car-outer-k
    (lambda (x ls k)
      `(rember-list-car-outer-k ,x ,ls ,k)))

  (define rember-list-car-inner-k
    (lambda (ra k)
      `(rember-list-car-inner-k ,ra ,k)))

  (define rember-else-k
    (lambda (ls k)
      `(rember-else-k ,ls ,k)))

  (define apply-ko
    (lambda (k^ v out)
      (conde
        [(== empty-k k^) (== v out)]
        [(fresh (x ls k a-ignore d)
           (== (rember-list-car-outer-k x ls k) k^)
           (== `(,a-ignore . ,d) ls)
           (rember*-cpso x d (rember-list-car-inner-k v k) out))]
        [(fresh (ra k)
           (== (rember-list-car-inner-k ra k) k^)
           (apply-ko k `(,ra . ,v) out))]
        [(fresh (ls k a d-ignore)
           (== (rember-else-k ls k) k^)
           (== `(,a . ,d-ignore) ls)
           (apply-ko k `(,a . ,v) out))])))

  (define rember*-cpso
    (lambda (x ls k out)
      (conde
        [(== '() ls) (apply-ko k '() out)]
        [(fresh (a d-ignore a1 a*)
           (== `(,a . ,d-ignore) ls)
           (== `(,a1 . ,a*) a)
           (rember*-cpso x a (rember-list-car-outer-k x ls k) out))]
        [(fresh (d)
           (== `(,x . ,d) ls)
           (rember*-cpso x d k out))]
        [(fresh (a d)
           (== `(,a . ,d) ls)
           (conde
             [(symbolo a)]
             [(== '() a)])
           (=/= a x)
           (rember*-cpso x d (rember-else-k ls k) out))])))

  (define rember*o
    (lambda (x ls out)
      (rember*-cpso x ls empty-k out)))

  (printf "*** vanilla CPS rembero*\n")

  (test "rember*o-1"
    (run* (q)
      (rember*o 'y '((x) (y) z y (w y y) v) q))
    '(((x) () z (w) v)))

  (test "rembero-1"
    (run* (q)
      (rember*o 'y '(x y z y w y y v) q))
    '((x z w v)))

  (test "rembero-2"
    (run* (q)
      (rember*o q '(x y z y w y y v) '(x z w v)))
    '(y))

  ;; diverges due to CPS!
  (test-disable "rember*o-3"
    (run 5 (q)
      (rember*o 'y q '(x z w v)))
    '((x z w v)
      (y x z w v)
      (x y z w v)
      (x z y w v)
      (x z w y v)))

  (test "rember*o-4"
    (run 5 (q)
      (fresh (x ls out)
        (rember*o x ls out)
        (== `(,x ,ls ,out) q)))
    '((_.0 () ())
      (_.0 (_.0) ())
      (_.0 (_.0 _.0) ())
      ((_.0 (_.1) (_.1)) (=/= ((_.0 _.1))) (sym _.1))
      ((_.0 (()) (())) (=/= ((_.0 ()))))))

  (test "rembero-5"
    (run* (q)
      (rember*o q '(x y) '(x z w y)))
    '())

;;; diverge
 (test-disable "rembero-6"
   (run 1 (q)
     (fresh (rest-a rest-b)
       (rember*o q `(x y . ,rest-a) `(x z w y . ,rest-b))))
   '())

;;; diverge
  (test-disable "rembero-7a"
    (run 1 (q)
      (rember*o 'x q '(x)))
    '())
;;; diverge
  (test-disable "rembero-7b"
    (run* (q)
      (rember*o 'x q '(x z w y)))
    '())

;;; diverges due to CPS
  (test-disable "rembero-8"
    (run* (q)
      (fresh (rest-a rest-b)
        (rember*o 'y `(x . ,rest-a) `(z . ,rest-b))))
    '())
  )

(let ()

  (define empty-k 'empty-k)

  (define rember-list-car-outer-k
    (lambda (x ls k)
      `(rember-list-car-outer-k ,x ,ls ,k)))

  (define rember-list-car-inner-k
    (lambda (ra k)
      `(rember-list-car-inner-k ,ra ,k)))

  (define rember-else-k
    (lambda (ls k)
      `(rember-else-k ,ls ,k)))

  (define apply-ko
    (lambda (k^ v out)
      (conde
        [(== empty-k k^) (== v out)]
        [(fresh (x ls k a-ignore d v-out-ignore)
           (== (rember-list-car-outer-k x ls k) k^)
           (== `(,a-ignore . ,d) ls)
           (rember*-cpso x d (rember-list-car-inner-k v k) out v-out-ignore))]
        [(fresh (ra k)
           (== (rember-list-car-inner-k ra k) k^)
           (apply-ko k `(,ra . ,v) out))]
        [(fresh (ls k a d-ignore)
           (== (rember-else-k ls k) k^)
           (== `(,a . ,d-ignore) ls)
           (apply-ko k `(,a . ,v) out))])))

  (define rember*-cpso
    (lambda (x ls k out v-out)
      (conde
        [(== '() ls) (== '() v-out) (apply-ko k '() out)]
        [(fresh (a d-ignore a1 a* v-out-ignore)
           (== `(,a . ,d-ignore) ls)
           (== `(,a1 . ,a*) a)
           (rember*-cpso x a (rember-list-car-outer-k x ls k) out v-out-ignore))]
        [(fresh (d)
           (== `(,x . ,d) ls)
           (rember*-cpso x d k out v-out))]
        [(fresh (a d v-out-d)
           (== `(,a . ,d) ls)
           (== `(,a . ,v-out-d) v-out)
           (conde
             [(symbolo a)]
             [(== '() a)])
           (=/= a x)
           (rember*-cpso x d (rember-else-k ls k) out v-out-d))])))

  (define rember*o
    (lambda (x ls out)
      (rember*-cpso x ls empty-k out out)))

;;; direct style rember*o, just for testing
  (define direct-rember*o
    (lambda (x ls out)
      (conde
        [(== '() ls) (== ls out)]
        [(fresh (a d ra rd a1 a*)
           (== `(,a . ,d) ls)
           (== `(,ra . ,rd) out)
           (== `(,a1 . ,a*) a)
           (direct-rember*o x a ra)
           (direct-rember*o x d rd))]
        [(fresh (d)
           (== `(,x . ,d) ls)
           (direct-rember*o x d out))]
        [(fresh (a d rd)
           (== `(,a . ,d) ls)
           (== `(,a . ,rd) out)
           (conde
             [(symbolo a)]
             [(== '() a)])
           (=/= a x)
           (direct-rember*o x d rd))])))

  (printf "*** direct-style rember*o with v-out\n")

  (test "rember*o-1"
    (run* (q)
      (rember*o 'y '((x) (y) z y (w y y) v) q))
    '(((x) () z (w) v)))

  (test "rembero-1"
    (run* (q)
      (rember*o 'y '(x y z y w y y v) q))
    '((x z w v)))

  (test "rembero-2"
    (run* (q)
      (rember*o q '(x y z y w y y v) '(x z w v)))
    '(y))

  ;; now, works again
  (test "rember*o-3"
    (run 5 (q)
      (rember*o 'y q '(x z w v)))
    '((x z w v)
      (x z w v y)
      (x z w y v)
      (x z y w v)
      (x y z w v)))

  (test "rember*o-4"
    (run 5 (q)
      (fresh (x ls out)
        (rember*o x ls out)
        (== `(,x ,ls ,out) q)))
    '((_.0 () ())
      (_.0 (_.0) ())
      (_.0 (_.0 _.0) ())
      ((_.0 (_.1) (_.1)) (=/= ((_.0 _.1))) (sym _.1))
      ((_.0 (()) (())) (=/= ((_.0 ()))))))

  (test "rembero-5"
    (run* (q)
      (rember*o q '(x y) '(x z w y)))
    '())

   (test "rember*o-b"
   (length
    (run 1000 (q)
      (fresh (x ls out)
        (== `(,x ,ls ,out) q)
        (direct-rember*o x ls out)
        (condu
          [(rember*o x ls out)]
          [(errorg 'rember*o-b "rember*o can't handle state generated by direct-rembero:\n\n~s\n\n" q)]))))
   1000)

 (test "rember*o-c"
   (length
    (run 1000 (q)
      (fresh (x ls out)
        (== `(,x ,ls ,out) q)
        (rember*o x ls out)
        (condu
          [(direct-rember*o x ls out)]
          [(errorg 'rember*o-c "direct-rember*o can't handle state generated by rembero:\n\n~s\n\n" q)]))))
   1000)

;;; diverge
 (test-disable "rembero-6"
   (run 1 (q)
     (fresh (rest-a rest-b)
       (rember*o q `(x y . ,rest-a) `(x z w y . ,rest-b))))
   '())

;;; diverge
  (test-disable "rembero-7a"
    (run 1 (q)
      (rember*o 'x q '(x)))
    '())
;;; diverge
  (test-disable "rembero-7b"
    (run* (q)
      (rember*o 'x q '(x z w y)))
    '())

;;; now, works again
  (test "rembero-8"
    (run* (q)
      (fresh (rest-a rest-b)
        (rember*o 'y `(x . ,rest-a) `(z . ,rest-b))))
    '())
  )
