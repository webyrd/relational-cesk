#!/usr/bin/env scheme-script
(import (rnrs) (mk-lib) (test-check-lib))

;;; examples of the v-out technique

;;; rembero

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
