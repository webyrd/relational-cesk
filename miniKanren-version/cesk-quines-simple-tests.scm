#!/usr/bin/env scheme-script
(import (rnrs) (mk-lib) (lookupo-lib) (cesk-quines-simple))

(define-syntax test
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'test
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))

(test "cesk-simple-quote-a"
  (run* (q)
    (evalo '(quote x) q))
  '(x))

(test "cesk-simple-quote"
  (run* (q)
    (evalo '(quote (lambda (x) x)) q))
  '((lambda (x) x)))

(test "cesk-simple-list-0"
  (run* (q)
    (evalo '(list) q))
  '(()))

(test "cesk-simple-closure"
  (run* (q)
    (evalo '(lambda (x) x) q))
  '((closure x x (() ()))))

(test "cesk-simple-identity-a"
  (run* (q)
    (evalo '((lambda (x) x) (lambda (y) y)) q))
  '((closure y y (() ()))))

(test "cesk-simple-identity-b"
  (run* (q)
    (evalo '((lambda (x) x) (quote foo)) q))
  '(foo))

(test "cesk-simple-list-1"
  (run* (q)
    (evalo '(list (quote foo)) q))
  '((foo)))

(test "cesk-simple-list-2"
  (run* (q)
    (evalo '(list (quote foo) (quote bar)) q))
  '((foo bar)))

(test "cesk-simple-list-1-backwards"
  (run 3 (q)
    (evalo q '(foo)))
  '('(foo)
    (list 'foo)
    (((lambda (_.0) '(foo)) '_.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1)))))

(test "cesk-simple-list-2-backwards"
  (run 3 (q)
    (fresh (x body)
      (evalo `(lambda (,x) ,body) '(foo))))
  '())

(test "cesk-simple-list-2b"
  (run 3 (q)
    (evalo q '(foo bar)))
  '('(foo bar)
    (list 'foo 'bar)
    (((lambda (_.0) '(foo bar)) '_.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1)))))

(test "cesk-simple-list-3"
  (run* (q)
    (evalo '(list (quote baz)
                  ((lambda (x) x) (list (quote foo) (quote bar)))
                  ((lambda (x) x) (list (quote quux))))
           q))
  '((baz (foo bar) (quux))))

(test "cesk-simple-shadowing"
  (run* (q)
    (evalo '((lambda (x)
               ((lambda (quote)
                  (quote x))
                (lambda (y) (list y y y))))
             (quote bar))
           q))
  '((bar bar bar)))

(test "cesk-simple-nested-lambda"
  (run* (q)
    (evalo '(((lambda (y)
                (lambda (x) y))
              (quote foo))
             (quote bar))
           q))
  '(foo))

(test "cesk-simple-fresh-bkwards"
  (run 10 (q)
    (fresh (expr v)
      (evalo expr v)
      (== `(,expr ,v) q)))
  '((('_.0 _.0) (absento (closure _.0)))
    (((lambda (_.0) _.1) (closure _.0 _.1 (() ()))) (sym _.0))
    ((list) ()) (((list '_.0) (_.0)) (absento (closure _.0)))
    (((list (lambda (_.0) _.1)) ((closure _.0 _.1 (() ()))))
     (sym _.0))
    (((list '_.0 '_.1) (_.0 _.1))
     (absento (closure _.0) (closure _.1)))
    ((((lambda (_.0) '_.1) '_.2) _.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (closure _.2)))
    ((((lambda (_.0) (lambda (_.1) _.2)) '_.3)
      (closure _.1 _.2 ((_.0) (_.4))))
     (=/= ((_.0 lambda)))
     (num _.4)
     (sym _.0 _.1)
     (absento (closure _.3)))
    (((list '_.0 (lambda (_.1) _.2))
      (_.0 (closure _.1 _.2 (() ()))))
     (sym _.1)
     (absento (closure _.0)))
    (((list (lambda (_.0) _.1) '_.2)
      ((closure _.0 _.1 (() ())) _.2))
     (sym _.0)
     (absento (closure _.2)))))
-
(test "cesk-simple-nested-lists"
  (run 4 (q)
    (fresh (expr k datum x y env^ env store val v-out a d)
      (== '(list (list)) expr)
      (eval-expo
       expr
       env
       store
       k
       val)
      (== `(,expr ,env ,store ,k ,val) q)))
  '((((list (list)) (_.0 _.1) _.2 (empty-k) (()))
     (absento (list _.0)))
    (((list (list)) (_.0 _.1) _.2 (list-aux-inner-k _.3 (empty-k)) (_.3 ()))
     (absento (list _.0)))
    (((list (list)) (_.0 _.1) (_.2 _.3) (application-inner-k (closure _.4 '_.5 (_.6 _.7)) (empty-k)) _.5)
     (=/= ((_.4 quote)))
     (sym _.4)
     (absento (closure _.5) (list _.0) '_.6))
    (((list (list)) (_.0 _.1) (_.2 _.3) (application-inner-k (closure _.4 (lambda (_.5) _.6) (_.7 _.8)) (empty-k)) (closure _.5 _.6 ((_.4 . _.7) (_.9 . _.8))))
     (=/= ((_.4 lambda)))
     (num _.9)
     (sym _.4 _.5)
     (absento (_.9 _.2) (lambda _.7) (list _.0)))))

(test "cesk-simple-empty-list-application"
  (run 4 (q)
    (fresh (expr k datum x y env^ env store val v-out a d)
      (== '((lambda (x) (quote (foo bar))) (list)) expr)
      (eval-expo
       expr
       env
       store
       k
       val)
      (== `(,expr ,env ,store ,k ,val) q)))
  '(((((lambda (x) '(foo bar)) (list))
      (_.0 _.1)
      (_.2 _.3)
      (empty-k)
      (foo bar))
     (absento (lambda _.0) (list _.0) '_.0))
    ((((lambda (x) '(foo bar)) (list))
      (_.0 _.1)
      (_.2 _.3)
      (list-aux-inner-k _.4 (empty-k))
      (_.4 foo bar))
     (absento (lambda _.0) (list _.0) '_.0))
    ((((lambda (x) '(foo bar)) (list))
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k (closure _.4 '_.5 (_.6 _.7)) (empty-k))
      _.5)
     (=/= ((_.4 quote)))
     (sym _.4)
     (absento (closure _.5) (lambda _.0) (list _.0) '_.0 '_.6))
    ((((lambda (x) '(foo bar)) (list))
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k
       (closure _.4 (lambda (_.5) _.6) (_.7 _.8))
       (empty-k))
      (closure _.5 _.6 ((_.4 . _.7) (_.9 . _.8))))
     (=/= ((_.4 lambda)))
     (num _.9)
     (sym _.4 _.5)
     (absento (_.9 _.2) (lambda _.0) (lambda _.7) (list _.0)
              '_.0))))

(test "cesk-simple-empty-list-non-empty-answer-backwards-1"
  (run 1 (q)
    (fresh (expr k datum x y env^ env store val)
      (== '(list) expr)
      (==
       `(application-inner-k
         (closure ,x (quote foo) ,env^)
         (empty-k))
       k)
      (eval-expo
       expr
       env
       store
       k
       val)
      (== `(,expr ,env ,store ,k ,val) q)))
  '((((list)
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k (closure _.4 'foo (_.5 _.6)) (empty-k))
      foo)
     (=/= ((_.4 quote)))
     (sym _.4)
     (absento (list _.0) '_.5))))

(test "cesk-simple-empty-list-non-empty-answer-backwards-2"
  (run 4 (q)
    (fresh (expr k datum x y env^ env store val a d)
      (== '(list) expr)
      (=/= '() val)
      (eval-expo
       expr
       env
       store
       k
       val)
      (== `(,expr ,env ,store ,k ,val) q)))
  '((((list)
      (_.0 _.1)
      _.2
      (list-aux-inner-k _.3 (empty-k))
      (_.3))
     (absento (list _.0)))
    (((list)
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k (closure _.4 '_.5 (_.6 _.7)) (empty-k))
      _.5)
     (=/= ((_.4 quote)) ((_.5 ())))
     (sym _.4)
     (absento (closure _.5) (list _.0) '_.6))
    (((list)
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k
       (closure _.4 (lambda (_.5) _.6) (_.7 _.8))
       (empty-k))
      (closure _.5 _.6 ((_.4 . _.7) (_.9 . _.8))))
     (=/= ((_.4 lambda)))
     (num _.9)
     (sym _.4 _.5)
     (absento (_.9 _.2) (lambda _.7) (list _.0)))
    (((list)
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k
       (closure _.4 '_.5 (_.6 _.7))
       (list-aux-inner-k _.8 (empty-k)))
      (_.8 . _.5))
     (=/= ((_.4 quote)))
     (sym _.4)
     (absento (closure _.5) (list _.0) '_.6))))

(define quinec
  '((lambda (x)
      (list x (list (quote quote) x)))
    (quote
      (lambda (x)
        (list x (list (quote quote) x))))))

(test "cesk-simple-quinec-forwards"
  (run* (q)
    (evalo quinec q))
  `(,quinec))

(test "cesk-simple-quinec-both"
  (run 1 (q)
    (evalo quinec quinec))
  '(_.0))

(test "cesk-simple-quote-bkwards-0"
  (run 1 (q)
    (evalo (quote (quote x)) (quote x)))
  `(_.0))

(test "cesk-simple-quote-bkwards-1"
  (run 1 (q)
    (evalo `(quote (quote x)) `(quote x)))
  `(_.0))

(test "cesk-simple-quote-bkwards-2"
  (run 1 (q)
      (fresh (y)
        (== y 'x)
        (eval-expo `(quote ,y)
                   empty-env
                   empty-store
                   empty-k
                   q)))
  `(x))

(test "cesk-simple-quinec-bkwards-a"
  (run 50 (q)
    (fresh (expr env store k val)
      (eval-expo
       expr
       env
       store
       k
       val)
      (== `(,expr ,env ,store ,k ,val) q)))
  '((('_.0 (_.1 _.2) _.3 (empty-k) _.0)
     (absento (closure _.0) '_.1))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      _.4
      (empty-k)
      (closure _.0 _.1 (_.2 _.3)))
     (sym _.0)
     (absento (lambda _.2)))
    (('_.0
      (_.1 _.2)
      _.3
      (list-aux-inner-k _.4 (empty-k))
      (_.4 . _.0))
     (absento (closure _.0) '_.1))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k (closure _.5 '_.6 (_.7 _.8)) (empty-k))
      _.6)
     (=/= ((_.5 quote)))
     (sym _.5)
     (absento (closure _.0) (closure _.6) '_.1 '_.7))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (_.5 . _.6))
          (empty-k)
          _.5)
     (num _.2)
     (sym _.0))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 (lambda (_.6) _.7) (_.8 _.9))
       (empty-k))
      (closure _.6 _.7 ((_.5 . _.8) (_.10 . _.9))))
     (=/= ((_.5 lambda)))
     (num _.10)
     (sym _.5 _.6)
     (absento (_.10 _.3) (closure _.0) (lambda _.8) '_.1))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      _.4
      (list-aux-inner-k _.5 (empty-k))
      (_.5 closure _.0 _.1 (_.2 _.3)))
     (sym _.0)
     (absento (lambda _.2)))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k (closure _.6 '_.7 (_.8 _.9)) (empty-k))
      _.7)
     (=/= ((_.6 quote)))
     (sym _.0 _.6)
     (absento (closure _.7) (lambda _.2) '_.8))
    (((list) (_.0 _.1) _.2 (empty-k) ()) (absento (list _.0)))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.2 . _.5) (_.6 _.7 . _.8))
          (empty-k)
          _.7)
     (=/= ((_.2 _.4)))
     (num _.2 _.4)
     (sym _.0))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 (lambda (_.7) _.8) (_.9 _.10))
       (empty-k))
      (closure _.7 _.8 ((_.6 . _.9) (_.11 . _.10))))
     (=/= ((_.6 lambda)))
     (num _.11)
     (sym _.0 _.6 _.7)
     (absento (_.11 _.4) (lambda _.2) (lambda _.9)))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (list-aux-inner-k _.9 (empty-k)))
      (_.9 . _.6))
     (=/= ((_.5 quote)))
     (sym _.5)
     (absento (closure _.0) (closure _.6) '_.1 '_.7))
    (('_.0
      (_.1 _.2)
      _.3
      (list-aux-outer-k (_.4) _.5 (empty-k))
      (_.0))
     (absento (closure _.0) '_.1))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (application-inner-k
        (closure _.9 '_.10 (_.11 _.12))
        (empty-k)))
      _.10)
     (=/= ((_.5 quote)) ((_.9 quote)))
     (sym _.5 _.9)
     (absento (closure _.0) (closure _.10) (closure _.6) '_.1
              '_.11 '_.7))
    ((_.0 ((_.1 _.0 . _.2) (_.3 _.4 . _.5))
          ((_.4 _.6 . _.7) (_.8 _.9 . _.10))
          (empty-k)
          _.8)
     (=/= ((_.0 _.1)))
     (num _.3 _.4 _.6)
     (sym _.0 _.1))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k (closure _.5 _.5 (_.6 _.7)) (empty-k))
      _.0)
     (sym _.5)
     (absento (closure _.0) '_.1))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (application-inner-k
        (closure _.9 (lambda (_.10) _.11) (_.12 _.13))
        (empty-k)))
      (closure _.10 _.11 ((_.9 . _.12) (_.14 . _.13))))
     (=/= ((_.5 quote)) ((_.9 lambda)))
     (num _.14)
     (sym _.10 _.5 _.9)
     (absento (_.14 _.3) (closure _.0) (closure _.6)
              (lambda _.12) '_.1 '_.7))
    (('_.0
      (_.1 _.2)
      _.3
      (list-aux-inner-k _.4 (list-aux-inner-k _.5 (empty-k)))
      (_.5 _.4 . _.0))
     (absento (closure _.0) '_.1))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (_.5 . _.6))
          (list-aux-inner-k _.7 (empty-k))
          (_.7 . _.5))
     (num _.2)
     (sym _.0))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (list-aux-inner-k
       _.5
       (application-inner-k
        (closure _.6 '_.7 (_.8 _.9))
        (empty-k)))
      _.7)
     (=/= ((_.6 quote)))
     (sym _.6)
     (absento (closure _.0) (closure _.7) '_.1 '_.8))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 (lambda (_.6) _.7) (_.8 _.9))
       (list-aux-inner-k _.10 (empty-k)))
      (_.10 closure _.6 _.7 ((_.5 . _.8) (_.11 . _.9))))
     (=/= ((_.5 lambda)))
     (num _.11)
     (sym _.5 _.6)
     (absento (_.11 _.3) (closure _.0) (lambda _.8) '_.1))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (_.5 . _.6))
          (application-inner-k
           (closure _.7 '_.8 (_.9 _.10))
           (empty-k))
          _.8)
     (=/= ((_.7 quote)))
     (num _.2)
     (sym _.0 _.7)
     (absento (closure _.8) '_.9))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 '_.7 (_.8 _.9))
       (list-aux-inner-k _.10 (empty-k)))
      (_.10 . _.7))
     (=/= ((_.6 quote)))
     (sym _.0 _.6)
     (absento (closure _.7) (lambda _.2) '_.8))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 (lambda (_.6) _.7) (_.8 _.9))
       (application-inner-k
        (closure _.10 '_.11 (_.12 _.13))
        (empty-k)))
      _.11)
     (=/= ((_.10 quote)) ((_.5 lambda)))
     (sym _.10 _.5 _.6)
     (absento (closure _.0) (closure _.11) (lambda _.8) '_.1
              '_.12))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      _.4
      (list-aux-outer-k (_.5) _.6 (empty-k))
      ((closure _.0 _.1 (_.2 _.3))))
     (sym _.0)
     (absento (lambda _.2)))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.5 _.2 . _.6) (_.7 _.8 _.9 . _.10))
          (empty-k)
          _.9)
     (=/= ((_.2 _.4)) ((_.2 _.5)))
     (num _.2 _.4 _.5)
     (sym _.0))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 '_.7 (_.8 _.9))
       (application-inner-k
        (closure _.10 '_.11 (_.12 _.13))
        (empty-k)))
      _.11)
     (=/= ((_.10 quote)) ((_.6 quote)))
     (sym _.0 _.10 _.6)
     (absento (closure _.11) (closure _.7) (lambda _.2) '_.12
              '_.8))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 (list) (_.6 _.7))
       (empty-k))
      ())
     (=/= ((_.5 list)))
     (sym _.5)
     (absento (closure _.0) (list _.6) '_.1))
    (((lambda (_.0) '_.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-outer-k '_.6 (_.7 _.8) (empty-k))
      _.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (closure _.6) (lambda _.2) '_.2
              '_.7))
    (('_.0
      (_.1 _.2)
      ((_.3 . _.4) (_.5 . _.6))
      (application-inner-k
       (closure _.7 _.8 ((_.8 . _.9) (_.10 . _.11)))
       (empty-k))
      _.0)
     (=/= ((_.10 _.3)) ((_.7 _.8)))
     (num _.10 _.3)
     (sym _.7 _.8)
     (absento (_.10 _.4) (closure _.0) '_.1))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k (closure _.6 _.6 (_.7 _.8)) (empty-k))
      (closure _.0 _.1 (_.2 _.3)))
     (sym _.0 _.6)
     (absento (lambda _.2)))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (list-aux-inner-k
       _.5
       (application-inner-k
        (closure _.6 (lambda (_.7) _.8) (_.9 _.10))
        (empty-k)))
      (closure _.7 _.8 ((_.6 . _.9) (_.11 . _.10))))
     (=/= ((_.6 lambda)))
     (num _.11)
     (sym _.6 _.7)
     (absento (_.11 _.3) (closure _.0) (lambda _.9) '_.1))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (_.5 . _.6))
          (application-inner-k
           (closure _.7 (lambda (_.8) _.9) (_.10 _.11))
           (empty-k))
          (closure _.8 _.9 ((_.7 . _.10) (_.12 . _.11))))
     (=/= ((_.12 _.2)) ((_.7 lambda)))
     (num _.12 _.2)
     (sym _.0 _.7 _.8)
     (absento (_.12 _.4) (lambda _.10)))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 (lambda (_.6) _.7) (_.8 _.9))
       (application-inner-k
        (closure _.10 (lambda (_.11) _.12) (_.13 _.14))
        (empty-k)))
      (closure _.11 _.12 ((_.10 . _.13) (_.15 . _.14))))
     (=/= ((_.10 lambda)) ((_.5 lambda)))
     (num _.15)
     (sym _.10 _.11 _.5 _.6)
     (absento (_.15 _.3) (closure _.0) (lambda _.13) (lambda _.8)
              '_.1))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 '_.7 (_.8 _.9))
       (application-inner-k
        (closure _.10 (lambda (_.11) _.12) (_.13 _.14))
        (empty-k)))
      (closure _.11 _.12 ((_.10 . _.13) (_.15 . _.14))))
     (=/= ((_.10 lambda)) ((_.6 quote)))
     (num _.15)
     (sym _.0 _.10 _.11 _.6)
     (absento (_.15 _.4) (closure _.7) (lambda _.13) (lambda _.2)
              '_.8))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      _.4
      (list-aux-inner-k _.5 (list-aux-inner-k _.6 (empty-k)))
      (_.6 _.5 closure _.0 _.1 (_.2 _.3)))
     (sym _.0)
     (absento (lambda _.2)))
    (((list)
      (_.0 _.1)
      _.2
      (list-aux-inner-k _.3 (empty-k))
      (_.3))
     (absento (list _.0)))
    (((lambda (_.0) (lambda (_.1) _.2))
      (_.3 _.4)
      (_.5 _.6)
      (application-outer-k '_.7 (_.8 _.9) (empty-k))
      (closure _.1 _.2 ((_.0 . _.3) (_.10 . _.4))))
     (=/= ((_.0 lambda)))
     (num _.10)
     (sym _.0 _.1)
     (absento (_.10 _.5) (closure _.7) (lambda _.3) '_.8))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.2 . _.5) (_.6 _.7 . _.8))
          (list-aux-inner-k _.9 (empty-k))
          (_.9 . _.7))
     (=/= ((_.2 _.4)))
     (num _.2 _.4)
     (sym _.0))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (list-aux-inner-k
       _.6
       (application-inner-k
        (closure _.7 '_.8 (_.9 _.10))
        (empty-k)))
      _.8)
     (=/= ((_.7 quote)))
     (sym _.0 _.7)
     (absento (closure _.8) (lambda _.2) '_.9))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 (lambda (_.7) _.8) (_.9 _.10))
       (list-aux-inner-k _.11 (empty-k)))
      (_.11 closure _.7 _.8 ((_.6 . _.9) (_.12 . _.10))))
     (=/= ((_.6 lambda)))
     (num _.12)
     (sym _.0 _.6 _.7)
     (absento (_.12 _.4) (lambda _.2) (lambda _.9)))
    (((list)
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k (closure _.4 '_.5 (_.6 _.7)) (empty-k))
      _.5)
     (=/= ((_.4 quote)))
     (sym _.4)
     (absento (closure _.5) (list _.0) '_.6))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.2 . _.5) (_.6 _.7 . _.8))
          (application-inner-k
           (closure _.9 '_.10 (_.11 _.12))
           (empty-k))
          _.10)
     (=/= ((_.2 _.4)) ((_.9 quote)))
     (num _.2 _.4)
     (sym _.0 _.9)
     (absento (closure _.10) '_.11))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 (lambda (_.7) _.8) (_.9 _.10))
       (application-inner-k
        (closure _.11 '_.12 (_.13 _.14))
        (empty-k)))
      _.12)
     (=/= ((_.11 quote)) ((_.6 lambda)))
     (sym _.0 _.11 _.6 _.7)
     (absento (closure _.12) (lambda _.2) (lambda _.9) '_.13))
    (('_.0
      (_.1 _.2)
      _.3
      (list-aux-outer-k
       (_.4)
       _.5
       (list-aux-inner-k _.6 (empty-k)))
      (_.6 _.0))
     (absento (closure _.0) '_.1))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (application-inner-k
        (closure _.9 '_.10 (_.11 _.12))
        (list-aux-inner-k _.13 (empty-k))))
      (_.13 . _.10))
     (=/= ((_.5 quote)) ((_.9 quote)))
     (sym _.5 _.9)
     (absento (closure _.0) (closure _.10) (closure _.6) '_.1
              '_.11 '_.7))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (list-aux-outer-k (_.9) _.10 (empty-k)))
      (_.6))
     (=/= ((_.5 quote)))
     (sym _.5)
     (absento (closure _.0) (closure _.6) '_.1 '_.7))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (list-aux-outer-k
       (_.5)
       _.6
       (application-inner-k
        (closure _.7 '_.8 (_.9 _.10))
        (empty-k)))
      _.8)
     (=/= ((_.7 quote)))
     (sym _.7)
     (absento (closure _.0) (closure _.8) '_.1 '_.9))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (application-inner-k
        (closure _.9 '_.10 (_.11 _.12))
        (application-inner-k
         (closure _.13 '_.14 (_.15 _.16))
         (empty-k))))
      _.14)
     (=/= ((_.13 quote)) ((_.5 quote)) ((_.9 quote)))
     (sym _.13 _.5 _.9)
     (absento (closure _.0) (closure _.10) (closure _.14)
              (closure _.6) '_.1 '_.11 '_.15 '_.7))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 (list) (_.7 _.8))
       (empty-k))
      ())
     (=/= ((_.6 list)))
     (sym _.0 _.6)
     (absento (lambda _.2) (list _.7)))))

(test "cesk-simple-quinec-bkwards-a"
  (run 1 (q)
    (== quinec q)
    (evalo q quinec))
  `(,quinec))

(test "cesk-simple-quinec-bkwards-c"
  (run 10 (q)
    (evalo q quinec))
  '('((lambda (x) (list x (list 'quote x)))
      '(lambda (x) (list x (list 'quote x))))
    (list
     '(lambda (x) (list x (list 'quote x)))
     ''(lambda (x) (list x (list 'quote x))))
    (((lambda (_.0)
        '((lambda (x) (list x (list 'quote x)))
          '(lambda (x) (list x (list 'quote x)))))
      '_.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1)))
    (((lambda (_.0) _.0)
      '((lambda (x) (list x (list 'quote x)))
        '(lambda (x) (list x (list 'quote x)))))
     (sym _.0))
    (((lambda (_.0)
        '((lambda (x) (list x (list 'quote x)))
          '(lambda (x) (list x (list 'quote x)))))
      (lambda (_.1) _.2))
     (=/= ((_.0 quote)))
     (sym _.0 _.1))
    (((lambda (_.0)
        '((lambda (x) (list x (list 'quote x)))
          '(lambda (x) (list x (list 'quote x)))))
      (list))
     (=/= ((_.0 quote)))
     (sym _.0))
    (((lambda (_.0)
        (list
         '(lambda (x) (list x (list 'quote x)))
         ''(lambda (x) (list x (list 'quote x)))))
      '_.1)
     (=/= ((_.0 list)) ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1)))
    (((lambda (_.0)
        ((lambda (_.1)
           '((lambda (x) (list x (list 'quote x)))
             '(lambda (x) (list x (list 'quote x)))))
         '_.2))
      '_.3)
     (=/= ((_.0 lambda)) ((_.0 quote)) ((_.1 quote)))
     (sym _.0 _.1)
     (absento (closure _.2) (closure _.3)))
    (((lambda (_.0)
        ((lambda (_.1)
           '((lambda (x) (list x (list 'quote x)))
             '(lambda (x) (list x (list 'quote x)))))
         (lambda (_.2) _.3)))
      '_.4)
     (=/= ((_.0 lambda)) ((_.0 quote)) ((_.1 quote)))
     (sym _.0 _.1 _.2)
     (absento (closure _.4)))
    (((lambda (_.0)
        (list
         '(lambda (x) (list x (list 'quote x)))
         ''(lambda (x) (list x (list 'quote x)))))
      (lambda (_.1) _.2))
     (=/= ((_.0 list)) ((_.0 quote)))
     (sym _.0 _.1))))

(test "cesk-simple-quinec-for-real"
  (run 1 (q)
    (evalo q q))
  '((((lambda (_.0) (list _.0 (list 'quote _.0)))
      '(lambda (_.0) (list _.0 (list 'quote _.0))))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))))

(test "cesk-simple-hard-quinec-bkwards-b"
  (run 1 (q)
    (evalo q quinec)
    (== quinec q))
  `(,quinec))

(test "twines"
  (run 1 (r)
    (fresh (p q)
      (=/= p q)
      (evalo p q)
      (evalo q p)
      (== `(,p ,q) r)))
  '((('((lambda (_.0)
          (list 'quote (list _.0 (list 'quote _.0))))
        '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0)))))
      ((lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))
       '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))))

(test "cesk-simple-quinec-for-real-3"
  (run 3 (q)
    (evalo q q))
  '((((lambda (_.0) (list _.0 (list 'quote _.0)))
      '(lambda (_.0) (list _.0 (list 'quote _.0))))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))
    (((lambda (_.0) (list _.0 (list 'quote ((lambda (_.1) _.0) '_.2))))
      '(lambda (_.0) (list _.0 (list 'quote ((lambda (_.1) _.0) '_.2)))))
     (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)))
     (sym _.0 _.1)
     (absento (closure _.2)))
    (((lambda (_.0)
        (list _.0 ((lambda (_.1) (list 'quote _.0)) '_.2)))
      '(lambda (_.0)
         (list _.0 ((lambda (_.1) (list 'quote _.0)) '_.2))))
     (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
     (sym _.0 _.1)
     (absento (closure _.2)))))
