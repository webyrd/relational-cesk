#!/usr/bin/env scheme-script
(import (rnrs) (mk-lib) (test-check-lib))

;;; examples of the v-out technique

(let ()

  (define rember
    (lambda (x ls)
      (cond
        [(null? ls) '()]
        [(eq? x (car ls)) (rember x (cdr ls))]
        [else
         (cons (car ls) (rember x (cdr ls)))])))

  (printf "*** vanilla direct-style Scheme remember\n")
  
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
           (rembero x d out))]
        [(fresh (a d res)
           (== `(,a . ,d) ls)
           (=/= a x)
           (== `(,a . ,res) out)
           (rembero x d res))])))

  (printf "*** vanilla direct-style remembero\n")
  
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

  (printf "*** direct-style remembero with v-out\n")
  
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
  
  (printf "*** CPS Scheme remember w/higher-order continuations\n")
  
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
  
  (printf "*** CPS Scheme remember w/higher-order (RI) continuations\n")
  
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
  
  (printf "*** CPS Scheme remember w/data-structural continuations\n")
  
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
  
  (printf "*** vanilla CPS remembero\n")
  
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

  )