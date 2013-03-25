(load "mk.scm")
(load "quines-lookupo.scm")
(load "test-check.scm")

(define answero
  (lambda (v s ans)
    (== `(,v . ,s) ans)))

(define not-in-envo
;;; with the old absento, this definition only works if x is a ground symbol
  (lambda (x env)
    (fresh (x*)
      (symbolo x)
      (env->x*o env x*)
      (absento x x*))))

(define not-in-storeo
  (lambda (addr store)
    (fresh (addr*)
      (numbero addr)
      (store->addr*o store addr*)
      (absento addr addr*))))

(define make-proco
  (lambda (x body env proc)
    (== `(closure ,x ,body ,env) proc)))

(define apply-proco
  (lambda (p a s^ k^ out v-out)
    (fresh (x body env addr env^ s^^)
      (make-proco x body env p)
      (ext-envo x addr env env^)
      (ext-storeo addr a s^ s^^)
      (numbero addr)
      (symbolo x)
      (not-in-storeo addr s^) ; not-in-storeo also calls numbero on addr--is this redundancy desireable?
      (eval-exp-auxo body env^ s^^ k^ out v-out) ; v-out
      )))

(define apply-ko
  (lambda (k^ v/s out v-out)
    (conde
      [(fresh (v s)
         (== '(empty-k) k^)
         (== v/s out)
         (answero v s v/s)
         (== v v-out)) ; v-out
       ]
      [(fresh (p k a s^^ v-out^)
         (== `(application-inner-k ,p ,k ,v-out^) k^)
         (answero a s^^ v/s)
         (apply-proco p a s^^ k out v-out^) ; v-out
         )]
      [(fresh (rand env k p s^ v-out^ v-out-ignore)
         (== `(application-outer-k ,rand ,env ,k ,v-out^) k^)
         (answero p s^ v/s)

;;; this isn't related to v-out, but p had better be a closure
;;;         
;;; ** the naive version of this fail-fast optimization is unsound in
;;; the presence of letcc/throw or call/cc! **
;;;
;;; This optimization results in different answer ordering. This makes
;;; testing trickier.
;;;
;;; A couple of rough benchmarks, using the version of this file shown at the Confo:
;;;         
;;; with this optimization:
;;; (time (load "cesk-quines.scm"))
;;;    2538 collections
;;;    73359 ms elapsed cpu time, including 4756 ms collecting
;;;    73404 ms elapsed real time, including 4740 ms collecting
;;;    21382279120 bytes allocated, including 21277591440 bytes reclaimed
;;;
;;; without the optimization--almost 5 times slower, and allocates more than
;;; 4 times as much memory.         
;;;
;;; (time (load "cesk-quines-no-fail-fast.scm"))
;;;    10507 collections
;;;    352053 ms elapsed cpu time, including 62634 ms collecting
;;;    352250 ms elapsed real time, including 62614 ms collecting
;;;    88514683712 bytes allocated, including 87976358640 bytes reclaimed
;;;
;;; To be meaningful, these benchmarks should be run under full Chez with optimizations and libraries.
;;; Still, the optimization clearly prunes the search tree in a beneficial way.

;;; On casper:
;;;         
;;; using petite on casper:
;;; (time (load "cesk-quines.scm"))
;;;   2723 collections
;;;   66097 ms elapsed cpu time, including 4484 ms collecting
;;;   66154 ms elapsed real time, including 4552 ms collecting
;;;   22941502176 bytes allocated, including 22849338064 bytes reclaimed
;;;         
;;; this code (with fail-fast optimization) under full Chez, with no optimization level specified:
;;; (time (load "cesk-quines.scm"))
;;;    180 collections
;;;    19078 ms elapsed cpu time, including 1547 ms collecting
;;;    19094 ms elapsed real time, including 1547 ms collecting
;;;    1518008288 bytes allocated, including 1412899056 bytes reclaimed
;;;
;;; full chez on casper, optimize level 2
;;; (time (load "cesk-quines.scm"))
;;;    180 collections
;;;    18991 ms elapsed cpu time, including 1538 ms collecting
;;;    19007 ms elapsed real time, including 1543 ms collecting
;;;    1518006048 bytes allocated, including 1412883360 bytes reclaimed
;;;
;;; full chez on casper, optimize level 3
;;; (time (load "cesk-quines.scm"))
;;;    174 collections
;;;    16894 ms elapsed cpu time, including 1517 ms collecting
;;;    16910 ms elapsed real time, including 1512 ms collecting
;;;    1467972880 bytes allocated, including 1357525632 bytes reclaimed
;;;
;;; full chez on casper, optimize level 3, **including the thrine test**
;;;
;;;(time (load "cesk-quines.scm"))
;;;    555 collections
;;;    80863 ms elapsed cpu time, including 6024 ms collecting
;;;    80911 ms elapsed real time, including 6041 ms collecting
;;;    4674773648 bytes allocated, including 4477361232 bytes reclaimed
         
         (fresh (x body env^)
           (make-proco x body env^ p))

         (eval-exp-auxo rand env s^ (application-inner-k p k v-out^) out v-out-ignore) ; v-out
         )]
      [(fresh (v k v* s^^ v-out-ignore ans)
         (== `(list-aux-inner-k ,v ,k) k^)
         (answero v* s^^ v/s)
         (== v* v-out) ; v-out
         (answero (cons v v*) s^^ ans)
         (apply-ko k ans out v-out-ignore))]
      [(fresh (e* env k v s^ e*-rest ignore v-out-rest)
         (== `(list-aux-outer-k ,e* ,env ,k ,v-out-rest) k^)
         (answero v s^ v/s)
         (== `(,ignore . ,e*-rest) e*)
         (list-auxo e*-rest env s^ (list-aux-inner-k v k) out v-out-rest))])))

(define empty-k '(empty-k))

;;; Is it necessary or desirable to make apply-ko representation-independent w.r.t. continuations?
;;; Not sure there is much benefit other than consistency, although that may be sufficient.
(define application-inner-k
  (lambda (p k v-out^)
    `(application-inner-k ,p ,k ,v-out^)))

(define application-outer-k
  (lambda (rand env k v-out^)
    `(application-outer-k ,rand ,env ,k ,v-out^)))

(define list-aux-inner-k
  (lambda (v k)
    `(list-aux-inner-k ,v ,k)))

(define list-aux-outer-k
  (lambda (e* env k v-out^)
    `(list-aux-outer-k ,e* ,env ,k ,v-out^)))

(define eval-exp-auxo
  (lambda (exp env s k out v-out)
    (conde
      [(fresh (datum ans)
         (== `(quote ,datum) exp)
         (== datum v-out) ; v-out
         (answero datum s ans)
         (absento 'closure datum)
         (not-in-envo 'quote env)
         (apply-ko k ans out v-out))]
      [(fresh (v ans)
         (== v v-out) ; v-out
         (symbolo exp)
         (answero v s ans)
         (lookupo exp env s v)
         (apply-ko k ans out v-out))]
      [(fresh (rator rand v-out-ignore)
         (== `(,rator ,rand) exp)
         (eval-exp-auxo rator env s (application-outer-k rand env k v-out) out v-out-ignore) ; v-out
         )]
      [(fresh (x body ans)
         (== `(lambda (,x) ,body) exp)
         (== (make-proc x body env) v-out) ; v-out
         (answero (make-proc x body env) s ans)
         (not-in-envo 'lambda env)
         (symbolo x) ; interesting: adding this symbolo constraint increased the runtime by ~7%
         (apply-ko k ans out v-out))]
      [(fresh (e*)
         (== `(list . ,e*) exp)
         (not-in-envo 'list env)
         (list-auxo e* env s k out v-out) ; v-out
         )])))

(define list-auxo
  (lambda (e* env s k out v-out*)
    (conde
      [(fresh (v-out-ignore ans)
         (== '() e*)
         (== '() v-out*) ; v-out*
         (answero '() s ans)
         (apply-ko k ans out v-out-ignore))]
      [(fresh (e ignore ignore^ v-out v-out-rest)
         (== `(,e . ,ignore) e*)
         (== `(,v-out . ,v-out-rest) v-out*) ; v-out*
         (eval-exp-auxo e env s (list-aux-outer-k e* env k v-out-rest) out v-out))])))

(define eval-expo
  (lambda (exp env s k out)
    (fresh (ans v s^ ignore)
      (answero v s^ ans)
      (== out v)
      (eval-exp-auxo exp env s k ans v))))

(define evalo
  (lambda (exp out)
    (eval-expo exp empty-env empty-store empty-k out)))

(test "cesk-quote-a"
  (run* (q)
    (evalo '(quote x) q))
  '(x))

(test "cesk-quote"
  (run* (q)
    (evalo '(quote (lambda (x) x)) q))
  '((lambda (x) x)))

(test "cesk-list-0"
  (run* (q)
    (evalo '(list) q))
  '(()))

(test "cesk-closure"
  (run* (q)
    (evalo '(lambda (x) x) q))
  '((closure x x (() ()))))

(test "cesk-identity-a"
  (run* (q)
    (evalo '((lambda (x) x) (lambda (y) y)) q))
  '((closure y y (() ()))))

(test "cesk-identity-b"
  (run* (q)
    (evalo '((lambda (x) x) (quote foo)) q))
  '(foo))

(test "cesk-list-1"
  (run* (q)
    (evalo '(list (quote foo)) q))
  '((foo)))

(test "cesk-list-2"
  (run* (q)
    (evalo '(list (quote foo) (quote bar)) q))
  '((foo bar)))

(test "cesk-list-1-backwards"
  (run 3 (q)
    (evalo q '(foo)))
  '('(foo)
    (list 'foo)
    (((lambda (_.0) '(foo)) '_.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1)))))

(test "cesk-list-2-backwards"
  (run 3 (q)
    (fresh (x body)
      (evalo `(lambda (,x) ,body) '(foo))))
  '())

(test "cesk-list-2b"
  (run 3 (q)
    (evalo q '(foo bar)))
  '('(foo bar)
    (list 'foo 'bar)
    (((lambda (_.0) '(foo bar)) '_.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1)))))

(test "cesk-list-3"
  (run* (q)
    (evalo '(list (quote baz)
                  ((lambda (x) x) (list (quote foo) (quote bar)))
                  ((lambda (x) x) (list (quote quux))))
           q))
  '((baz (foo bar) (quux))))

(test "cesk-shadowing"
  (run* (q)
    (evalo '((lambda (x)
               ((lambda (quote)
                  (quote x))
                (lambda (y) (list y y y))))
             (quote bar))
           q))
  '((bar bar bar)))

(define quinec
  '((lambda (x)
      (list x (list (quote quote) x)))
    (quote
      (lambda (x)
        (list x (list (quote quote) x))))))

(test "cesk-quinec-forwards"
  (run* (q)
    (evalo quinec q))
  `(,quinec))

(test "cesk-quinec-both"
  (run 1 (q)
    (evalo quinec quinec))
  '(_.0))

(test "cesk-quote-bkwards-0"
  (run 1 (q)
    (evalo (quote (quote x)) (quote x)))
  `(_.0))

(test "cesk-quote-bkwards-1"
  (run 1 (q)
    (evalo `(quote (quote x)) `(quote x)))
  `(_.0))

(test "cesk-quote-bkwards-2"
  (run 1 (q)
      (fresh (y)
        (== y 'x)
        (eval-expo `(quote ,y)
                   empty-env
                   empty-store
                   empty-k
                   q)))
  `(x))

;;; generate k here
(test "cesk-quinec-bkwards-a"
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
       (closure _.5 '_.0 (_.6 _.7))
       (empty-k)
       _.0)
      _.0)
     (=/= ((_.5 quote)))
     (sym _.5)
     (absento (closure _.0) '_.1 '_.6))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      _.4
      (empty-k)
      (closure _.0 _.1 (_.2 _.3)))
     (sym _.0)
     (absento (lambda _.2)))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.2 . _.5) (_.6 _.7 . _.8))
          (empty-k)
          _.7)
     (=/= ((_.2 _.4)))
     (num _.2 _.4)
     (sym _.0))
    (((list) (_.0 _.1) _.2 (empty-k) ()) (absento (list _.0)))
    ((_.0 ((_.1 _.0 . _.2) (_.3 _.4 . _.5))
          ((_.4 _.6 . _.7) (_.8 _.9 . _.10))
          (empty-k)
          _.8)
     (=/= ((_.0 _.1)))
     (num _.3 _.4 _.6)
     (sym _.0 _.1))
    (('(_.0 . _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 '_.1 (_.7 _.8))
       (list-aux-inner-k _.0 (empty-k))
       _.1)
      (_.0 . _.1))
     (=/= ((_.6 quote)))
     (sym _.6)
     (absento (closure _.0) (closure _.1) '_.2 '_.7))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 _.5 (_.6 _.7))
       (empty-k)
       _.0)
      _.0)
     (sym _.5)
     (absento (closure _.0) '_.1))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (list-aux-inner-k
       _.5
       (application-inner-k
        (closure _.6 '_.0 (_.7 _.8))
        (empty-k)
        _.0))
      _.0)
     (=/= ((_.6 quote)))
     (sym _.6)
     (absento (closure _.0) '_.1 '_.7))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (_.5 . _.6))
          (application-inner-k
           (closure _.7 '_.5 (_.8 _.9))
           (empty-k)
           _.5)
          _.5)
     (=/= ((_.7 quote)))
     (num _.2)
     (sym _.0 _.7)
     (absento (closure _.5) '_.8))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.5 _.2 . _.6) (_.7 _.8 _.9 . _.10))
          (empty-k)
          _.9)
     (=/= ((_.2 _.4)) ((_.2 _.5)))
     (num _.2 _.4 _.5)
     (sym _.0))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (application-inner-k
        (closure _.9 '_.0 (_.10 _.11))
        (empty-k)
        _.0)
       _.6)
      _.0)
     (=/= ((_.5 quote)) ((_.9 quote)))
     (sym _.5 _.9)
     (absento (closure _.0) (closure _.6) '_.1 '_.10 '_.7))
    (('_.0
      (_.1 _.2)
      ((_.3 . _.4) (_.5 . _.6))
      (application-inner-k
       (closure _.7 _.8 ((_.8 . _.9) (_.10 . _.11)))
       (empty-k)
       _.0)
      _.0)
     (=/= ((_.10 _.3)) ((_.7 _.8)))
     (num _.10 _.3)
     (sym _.7 _.8)
     (absento (_.10 _.4) (closure _.0) '_.1))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.2 . _.5) (_.6 _.7 . _.8))
          (application-inner-k
           (closure _.9 '_.7 (_.10 _.11))
           (empty-k)
           _.7)
          _.7)
     (=/= ((_.2 _.4)) ((_.9 quote)))
     (num _.2 _.4)
     (sym _.0 _.9)
     (absento (closure _.7) '_.10))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (list-aux-outer-k
       (_.5)
       _.6
       (application-inner-k
        (closure _.7 '_.0 (_.8 _.9))
        (empty-k)
        _.0)
       ())
      _.0)
     (=/= ((_.7 quote)))
     (sym _.7)
     (absento (closure _.0) '_.1 '_.8))
    (('(_.0)
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.0 (_.6 _.7))
       (list-aux-outer-k (_.8) _.9 (empty-k) ())
       _.0)
      (_.0))
     (=/= ((_.5 quote)))
     (sym _.5)
     (absento (closure _.0) '_.1 '_.6))
    (('() (_.0 _.1)
      (_.2 _.3)
      (application-inner-k
       (closure _.4 (list) (_.5 _.6))
       (empty-k)
       ())
      ())
     (=/= ((_.4 list)))
     (sym _.4)
     (absento (list _.5) '_.0))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.5 _.6 _.2 . _.7) (_.8 _.9 _.10 _.11 . _.12))
          (empty-k)
          _.11)
     (=/= ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)))
     (num _.2 _.4 _.5 _.6)
     (sym _.0))
    (('(_.0 . _.1)
      (_.2 _.3)
      (_.4 _.5)
      (list-aux-inner-k
       _.6
       (application-inner-k
        (closure _.7 '_.1 (_.8 _.9))
        (list-aux-inner-k _.0 (empty-k))
        _.1))
      (_.0 . _.1))
     (=/= ((_.7 quote)))
     (sym _.7)
     (absento (closure _.0) (closure _.1) '_.2 '_.8))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) ((_.5 . _.6) . _.7))
          (application-inner-k
           (closure _.8 '_.6 (_.9 _.10))
           (list-aux-inner-k _.5 (empty-k))
           _.6)
          (_.5 . _.6))
     (=/= ((_.8 quote)))
     (num _.2)
     (sym _.0 _.8)
     (absento (closure _.6) '_.9))
    (('_.0
      (_.1 _.2)
      ((_.3 . _.4) (_.0 . _.5))
      (application-inner-k
       (closure _.6 _.7 ((_.7 . _.8) (_.3 . _.9)))
       (empty-k)
       _.0)
      _.0)
     (=/= ((_.6 _.7)))
     (num _.3)
     (sym _.6 _.7)
     (absento (closure _.0) '_.1))
    (('(_.0 . _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 '_.7 (_.8 _.9))
       (application-inner-k
        (closure _.10 '_.1 (_.11 _.12))
        (list-aux-inner-k _.0 (empty-k))
        _.1)
       _.7)
      (_.0 . _.1))
     (=/= ((_.10 quote)) ((_.6 quote)))
     (sym _.10 _.6)
     (absento (closure _.0) (closure _.1) (closure _.7) '_.11
              '_.2 '_.8))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (_.5 . _.6))
          (application-inner-k
           (closure _.7 _.7 (_.8 _.9))
           (empty-k)
           _.5)
          _.5)
     (num _.2)
     (sym _.0 _.7))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.0 (_.6 _.7))
       (application-inner-k
        (closure _.8 _.8 (_.9 _.10))
        (empty-k)
        _.0)
       _.0)
      _.0)
     (=/= ((_.5 quote)))
     (sym _.5 _.8)
     (absento (closure _.0) '_.1 '_.6))
    (('(_.0 _.1 . _.2)
      (_.3 _.4)
      (_.5 _.6)
      (application-inner-k
       (closure _.7 '_.2 (_.8 _.9))
       (list-aux-inner-k _.1 (list-aux-inner-k _.0 (empty-k)))
       _.2)
      (_.0 _.1 . _.2))
     (=/= ((_.7 quote)))
     (sym _.7)
     (absento (closure _.0) (closure _.1) (closure _.2) '_.3
              '_.8))
    (((list)
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k
       (closure _.4 '() (_.5 _.6))
       (empty-k)
       ())
      ())
     (=/= ((_.4 quote)))
     (sym _.4)
     (absento (list _.0) '_.5))
    ((_.0 ((_.1 _.0 . _.2) (_.3 _.4 . _.5))
          ((_.4 _.6 . _.7) (_.8 _.9 . _.10))
          (application-inner-k
           (closure _.11 '_.8 (_.12 _.13))
           (empty-k)
           _.8)
          _.8)
     (=/= ((_.0 _.1)) ((_.11 quote)))
     (num _.3 _.4 _.6)
     (sym _.0 _.1 _.11)
     (absento (closure _.8) '_.12))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (list-aux-inner-k
        _.9
        (application-inner-k
         (closure _.10 '_.0 (_.11 _.12))
         (empty-k)
         _.0))
       _.6)
      _.0)
     (=/= ((_.10 quote)) ((_.5 quote)))
     (sym _.10 _.5)
     (absento (closure _.0) (closure _.6) '_.1 '_.11 '_.7))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 _.5 (_.6 _.7))
       (application-inner-k
        (closure _.8 '_.0 (_.9 _.10))
        (empty-k)
        _.0)
       _.0)
      _.0)
     (=/= ((_.8 quote)))
     (sym _.5 _.8)
     (absento (closure _.0) '_.1 '_.9))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (list-aux-inner-k
       _.5
       (application-inner-k
        (closure _.6 '_.7 (_.8 _.9))
        (application-inner-k
         (closure _.10 '_.0 (_.11 _.12))
         (empty-k)
         _.0)
        _.7))
      _.0)
     (=/= ((_.10 quote)) ((_.6 quote)))
     (sym _.10 _.6)
     (absento (closure _.0) (closure _.7) '_.1 '_.11 '_.8))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (_.5 . _.6))
          (application-inner-k
           (closure _.7 '_.8 (_.9 _.10))
           (application-inner-k
            (closure _.11 '_.5 (_.12 _.13))
            (empty-k)
            _.5)
           _.8)
          _.5)
     (=/= ((_.11 quote)) ((_.7 quote)))
     (num _.2)
     (sym _.0 _.11 _.7)
     (absento (closure _.5) (closure _.8) '_.12 '_.9))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (application-inner-k
        (closure _.9 '_.10 (_.11 _.12))
        (application-inner-k
         (closure _.13 '_.0 (_.14 _.15))
         (empty-k)
         _.0)
        _.10)
       _.6)
      _.0)
     (=/= ((_.13 quote)) ((_.5 quote)) ((_.9 quote)))
     (sym _.13 _.5 _.9)
     (absento (closure _.0) (closure _.10) (closure _.6) '_.1
              '_.11 '_.14 '_.7))
    ((_.0 ((_.1 _.0 . _.2) (_.3 _.4 . _.5))
          ((_.6 _.4 . _.7) (_.8 _.9 . _.10))
          (empty-k)
          _.9)
     (=/= ((_.0 _.1)) ((_.4 _.6)))
     (num _.3 _.4 _.6)
     (sym _.0 _.1))
    (('_.0
      (_.1 _.2)
      ((_.3 _.4 . _.5) (_.6 _.7 . _.8))
      (application-inner-k
       (closure _.9 _.10 ((_.11 _.10 . _.12) (_.13 _.14 . _.15)))
       (empty-k)
       _.0)
      _.0)
     (=/= ((_.10 _.11)) ((_.10 _.9)) ((_.14 _.3)) ((_.14 _.4)))
     (num _.13 _.14 _.3 _.4)
     (sym _.10 _.11 _.9)
     (absento (_.14 _.5) (closure _.0) '_.1))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4)
           ((closure _.5 _.6 ((_.7 . _.8) (_.9 . _.10))) . _.11))
          (application-inner-k
           (closure _.7 (lambda (_.5) _.6) (_.8 _.10))
           (empty-k)
           (closure _.5 _.6 ((_.7 . _.8) (_.9 . _.10))))
          (closure _.5 _.6 ((_.7 . _.8) (_.9 . _.10))))
     (=/= ((_.2 _.9)) ((_.7 lambda)))
     (num _.2 _.9)
     (sym _.0 _.5 _.7)
     (absento (_.9 _.4) (lambda _.8)))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 '(_.0 _.1 (_.2 _.3)) (_.7 _.8))
       (list-aux-inner-k closure (empty-k))
       (_.0 _.1 (_.2 _.3)))
      (closure _.0 _.1 (_.2 _.3)))
     (=/= ((_.0 closure)) ((_.6 quote)))
     (sym _.0 _.6)
     (absento (closure _.1) (closure _.2) (closure _.3)
              (lambda _.2) '_.7))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (_.5 . _.6))
          (application-inner-k
           (closure _.7 _.8 ((_.8 . _.9) (_.10 . _.11)))
           (empty-k)
           _.5)
          _.5)
     (=/= ((_.10 _.2)) ((_.7 _.8)))
     (num _.10 _.2)
     (sym _.0 _.7 _.8)
     (absento (_.10 _.4)))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.0 (_.6 _.7))
       (application-inner-k
        (closure _.8 _.9 ((_.9 . _.10) (_.11 . _.12)))
        (empty-k)
        _.0)
       _.0)
      _.0)
     (=/= ((_.5 quote)) ((_.8 _.9)))
     (num _.11)
     (sym _.5 _.8 _.9)
     (absento (_.11 _.3) (closure _.0) '_.1 '_.6))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.2 . _.5) (_.6 (_.7 . _.8) . _.9))
          (application-inner-k
           (closure _.10 '_.8 (_.11 _.12))
           (list-aux-inner-k _.7 (empty-k))
           _.8)
          (_.7 . _.8))
     (=/= ((_.10 quote)) ((_.2 _.4)))
     (num _.2 _.4)
     (sym _.0 _.10)
     (absento (closure _.8) '_.11))
    (((list '_.0) (_.1 _.2) _.3 (empty-k) (_.0))
     (absento (closure _.0) (list _.1) '_.1))
    (('(_.0 . _.1)
      (_.2 _.3)
      (_.4 _.5)
      (list-aux-outer-k
       (_.6)
       _.7
       (application-inner-k
        (closure _.8 '_.1 (_.9 _.10))
        (list-aux-inner-k _.0 (empty-k))
        _.1)
       ())
      (_.0 . _.1))
     (=/= ((_.8 quote)))
     (sym _.8)
     (absento (closure _.0) (closure _.1) '_.2 '_.9))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 _.6 (_.7 _.8))
       (empty-k)
       (closure _.0 _.1 (_.2 _.3)))
      (closure _.0 _.1 (_.2 _.3)))
     (sym _.0 _.6)
     (absento (lambda _.2)))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.2 . _.5) (_.6 _.7 . _.8))
          (application-inner-k
           (closure _.9 _.9 (_.10 _.11))
           (empty-k)
           _.7)
          _.7)
     (=/= ((_.2 _.4)))
     (num _.2 _.4)
     (sym _.0 _.9))
    (('(_.0 _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 '_.1 (_.7 _.8))
       (list-aux-outer-k
        (_.9)
        _.10
        (list-aux-inner-k _.0 (empty-k))
        ())
       _.1)
      (_.0 _.1))
     (=/= ((_.6 quote)))
     (sym _.6)
     (absento (closure _.0) (closure _.1) '_.2 '_.7))
    (((_.0 '_.1)
      ((_.0 . _.2) (_.3 . _.4))
      ((_.3 . _.5) ((closure _.6 '_.7 (_.8 _.9)) . _.10))
      (empty-k)
      _.7)
     (=/= ((_.0 quote)) ((_.6 quote)))
     (num _.3)
     (sym _.0 _.6)
     (absento (closure _.1) (closure _.7) '_.2 '_.8))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (list-aux-inner-k
       _.5
       (list-aux-inner-k
        _.6
        (application-inner-k
         (closure _.7 '_.0 (_.8 _.9))
         (empty-k)
         _.0)))
      _.0)
     (=/= ((_.7 quote)))
     (sym _.7)
     (absento (closure _.0) '_.1 '_.8))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (_.5 . _.6))
          (list-aux-inner-k
           _.7
           (application-inner-k
            (closure _.8 '_.5 (_.9 _.10))
            (empty-k)
            _.5))
          _.5)
     (=/= ((_.8 quote)))
     (num _.2)
     (sym _.0 _.8)
     (absento (closure _.5) '_.9))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 (lambda (_.6) _.7) (_.8 _.9))
       (application-inner-k
        (closure _.10 '_.0 (_.11 _.12))
        (empty-k)
        _.0)
       (closure _.6 _.7 ((_.5 . _.8) (_.13 . _.9))))
      _.0)
     (=/= ((_.10 quote)) ((_.5 lambda)))
     (num _.13)
     (sym _.10 _.5 _.6)
     (absento (_.13 _.3) (closure _.0) (lambda _.8) '_.1 '_.11))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.5 _.2 . _.6) (_.7 _.8 _.9 . _.10))
          (application-inner-k
           (closure _.11 '_.9 (_.12 _.13))
           (empty-k)
           _.9)
          _.9)
     (=/= ((_.11 quote)) ((_.2 _.4)) ((_.2 _.5)))
     (num _.2 _.4 _.5)
     (sym _.0 _.11)
     (absento (closure _.9) '_.12))))

(test "cesk-quinec-bkwards-a"
  (run 1 (q)
    (== quinec q)
    (evalo q quinec))
  `(,quinec))

(test "cesk-quinec-bkwards-c"
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
    (list
     '(lambda (x) (list x (list 'quote x)))
     (list 'quote '(lambda (x) (list x (list 'quote x)))))
    (((lambda (_.0)
        '((lambda (x) (list x (list 'quote x)))
          '(lambda (x) (list x (list 'quote x)))))
      (list))
     (=/= ((_.0 quote)))
     (sym _.0))
    ((list
      '(lambda (x) (list x (list 'quote x)))
      ((lambda (_.0) ''(lambda (x) (list x (list 'quote x))))
       '_.1))
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1)))
    (((lambda (_.0)
        (list
         '(lambda (x) (list x (list 'quote x)))
         ''(lambda (x) (list x (list 'quote x)))))
      '_.1)
     (=/= ((_.0 list)) ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1)))
    (list
     (list 'lambda '(x) '(list x (list 'quote x)))
     ''(lambda (x) (list x (list 'quote x))))))

(test "cesk-fresh-bkwards"
  (run 10 (q)
    (fresh (expr v)
      (evalo expr v)
      (== `(,expr ,v) q)))
  '((('_.0 _.0) (absento (closure _.0))) (((lambda (_.0) _.1) (closure _.0 _.1 (() ()))) (sym _.0))
    ((list) ()) (((list '_.0) (_.0)) (absento (closure _.0)))
    (((list '_.0 '_.1) (_.0 _.1))
     (absento (closure _.0) (closure _.1)))
    (((list (lambda (_.0) _.1)) ((closure _.0 _.1 (() ()))))
     (sym _.0))
    ((((lambda (_.0) '_.1) '_.2) _.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (closure _.2)))
    ((((lambda (_.0) _.0) '_.1) _.1)
     (sym _.0)
     (absento (closure _.1)))
    ((list (list)) (()))
    ((((lambda (_.0) (lambda (_.1) _.2)) '_.3)
      (closure _.1 _.2 ((_.0) (_.4))))
     (=/= ((_.0 lambda)))
     (num _.4)
     (sym _.0 _.1)
     (absento (closure _.3)))))

(test "cesk-quinec-for-real"
  (run 1 (q)
    (evalo q q))
  '((((lambda (_.0) (list _.0 (list 'quote _.0)))
      '(lambda (_.0) (list _.0 (list 'quote _.0))))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))))

(test "cesk-hard-quinec-bkwards-b"
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

(test "cesk-quinec-for-real-3"
  (run 3 (q)
    (evalo q q))
  '((((lambda (_.0) (list _.0 (list 'quote _.0)))
      '(lambda (_.0) (list _.0 (list 'quote _.0))))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))
    (((lambda (_.0)
        (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0)))
      '(lambda (_.0)
         (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0))))
     (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
          ((_.0 quote)) ((_.1 closure)) ((_.1 quote)))
     (sym _.0 _.1)
     (absento (closure _.2)))
    (((lambda (_.0)
        (list (list 'lambda '(_.0) _.0) (list 'quote _.0)))
      '(list (list 'lambda '(_.0) _.0) (list 'quote _.0)))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))))

#!eof

;;; comes back under full chez in about 60 seconds
;;; would probably be waiting at least 3x as long under petite, if it doesn't run out of memory.
(test "thrine"
  (run 1 (x)
    (fresh (p q r)
      (=/= p q)
      (=/= q r)
      (=/= r p)
      (evalo p q)
      (evalo q r)
      (evalo r p)
      (== `(,p ,q ,r) x)))
  '(((''((lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0))))) '(lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0))))))
      '((lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0))))) '(lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0))))))
      ((lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0))))) '(lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))))

