(load "mk.scm")
(load "quines-lookupo.scm")
(load "test-check.scm")

(define answer
  (lambda (v s)
    (cons v s)))

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

(define make-proc
  (lambda (x body env)
    `(closure ,x ,body ,env)))

(define apply-proco
  (lambda (p a s^ k^ out v-out)
    (fresh (x body env addr env^ s^^)
      (== (make-proc x body env) p)
      (ext-envo x addr env env^)
      (ext-storeo addr a s^ s^^)
      (numbero addr)
      (symbolo x)
      (not-in-storeo addr s^) ; not-in-storeo also calls numbero on addr--is this redundancy desireable?
      (eval-exp-auxo body env^ s^^ k^ out v-out) ; v-out (this use is essential--passing a fresh variable results in the ability to generate quines in a reasonable time)
      )))

(define apply-ko
  (lambda (k^ v/s out)
    (conde
      [(fresh (v s)
         (== empty-k k^)
         (== v/s out)
         (== (answer v s) v/s))
       ]
      [(fresh (p k a s^^ v-out^)
         (== (application-inner-k p k v-out^) k^)
         (== (answer a s^^) v/s)
         (apply-proco p a s^^ k out v-out^) ; v-out (this use is essential--passing a fresh variable results in the ability to generate quines in a reasonable time)
         )]
      [(fresh (rand env k p s^ v-out^ v-out-ignore)
         (== (application-outer-k rand env k v-out^) k^)
         (== (answer p s^) v/s)

;;; this isn't related to v-out, but p had better be a closure
;;;
;;; ** the naive version of this fail-fast optimization is unsound in
;;; the presence of letcc/throw or call/cc! **
;;;
;;; This optimization results in different answer ordering. This makes
;;; testing trickier.         
         (fresh (x body env^)
           (== (make-proc x body env^) p))

         (eval-exp-auxo rand env s^ (application-inner-k p k v-out^) out v-out-ignore) ; v-out (this use is essential--passing a fresh variable results in the ability to generate quines in a reasonable time)
         )]
      [(fresh (v k v* s^^ ans)
         (== (list-aux-inner-k v k) k^)
         (== (answer v* s^^) v/s)
         (== (answer (cons v v*) s^^) ans)
         (apply-ko k ans out))]
      [(fresh (e* env k v s^ e*-rest ignore v-out-rest)
         (== (list-aux-outer-k e* env k v-out-rest) k^)
         (== (answer v s^) v/s)
         (== `(,ignore . ,e*-rest) e*)
         (list-auxo e*-rest env s^ (list-aux-inner-k v k) out v-out-rest) ; v-out (this use is essential--passing a fresh variable results in the ability to generate quines in a reasonable time)
         )])))

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
;         (== datum v-out) ; v-out  this use isn't strictly needed--without it, quine generation takes 2.4 seconds rather than 800 ms
;         ** This unification causes 'cesk-application-inner-k-2' to fail. **
;          Is there a way prune the search tree for simple expressions, without overconstraining the answer?
         (== (answer datum s) ans)
         (absento 'closure datum)
         (not-in-envo 'quote env)
         (apply-ko k ans out))]
      [(fresh (x body ans)
         (== `(lambda (,x) ,body) exp)
;         (== (make-proc x body env) v-out) ; v-out
         (== (answer (make-proc x body env) s) ans)
         (not-in-envo 'lambda env)
         (symbolo x) ; interesting: adding this symbolo constraint increased the runtime by ~7%
         (apply-ko k ans out))]
      [(fresh (v ans)
;         (== v v-out) ; v-out
         (symbolo exp)
         (== (answer v s) ans)
         (lookupo exp env s v)
         (apply-ko k ans out))]
      [(fresh (rator rand v-out-ignore)
         (== `(,rator ,rand) exp)
         (eval-exp-auxo rator env s (application-outer-k rand env k v-out) out v-out-ignore) ; v-out
         )]
      [(fresh (e*)
         (== `(list . ,e*) exp)
         (not-in-envo 'list env)
         (list-auxo e* env s k out v-out) ; v-out
         )])))

(define list-auxo
  (lambda (e* env s k out v-out*)
    (conde
      [(fresh (ans)
         (== '() e*)
;         (== '() v-out*) ; v-out*
         (== (answer '() s) ans)
         (apply-ko k ans out))]
      [(fresh (e ignore ignore^ v-out v-out-rest)
         (== `(,e . ,ignore) e*)
         (== `(,v-out . ,v-out-rest) v-out*) ; v-out*
         (eval-exp-auxo e env s (list-aux-outer-k e* env k v-out-rest) out v-out))])))

(define eval-expo
  (lambda (exp env s k out)
    (fresh (ans s^ v-out)
      (== (answer out s^) ans)
      (== out v-out) ; v-out
      (eval-exp-auxo exp env s k ans v-out))))

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
    (((lambda (_.0) '(foo bar)) '_.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1)))
    (list 'foo 'bar)))

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

(test "cesk-nested-lambda"
  (run* (q)
    (evalo '(((lambda (y)
                (lambda (x) y))
              (quote foo))
             (quote bar))
           q))
  '(foo))

;;; tests related to v-out
(test "cesk-application-inner-k-1"
  (run 1 (q)
    (fresh (expr env store k val v-out datum env^ x datum^)
      (== `(quote ,datum) expr)
      (==
       `(application-inner-k
         (closure ,x (quote ,datum^) ,env^)
         (empty-k)
         ,v-out)
       k)
      (eval-expo
       expr
       env
       store
       k
       val)
      (== `(,expr ,env ,store ,k ,val) q)))
  '((((quote _.0)
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k (closure _.5 (quote _.6) (_.7 _.8)) (empty-k) _.9)
      _.6)
     (=/= ((_.5 quote)))
     (sym _.5)
     (absento (closure _.0) (closure _.6) (quote _.1) (quote _.7)))))

(test "cesk-application-inner-k-2"
  (run 4 (q)
    (fresh (expr k datum x y env^ env store val v-out)
      (== `(quote ,datum) expr)
      (symbolo y)
      (==
       `(application-inner-k
         (closure ,x ,y ,env^)
         (empty-k)
         ,v-out)
       k)
      (eval-expo
       expr
       env
       store
       k
       val)
      (== `(,expr ,env ,store ,k ,val) q)))
  '((((quote _.0)
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 _.5 (_.6 _.7))
       (empty-k)
       _.8)
      _.0)
     (sym _.5)
     (absento (closure _.0) (quote _.1)))
    (((quote _.0)
      (_.1 _.2)
      ((_.3 . _.4) (_.5 . _.6))
      (application-inner-k
       (closure _.7 _.8 ((_.8 . _.9) (_.10 . _.11)))
       (empty-k)
       _.12)
      _.0)
     (=/= ((_.10 _.3)) ((_.7 _.8)))
     (num _.10 _.3)
     (sym _.7 _.8)
     (absento (_.10 _.4) (closure _.0) (quote _.1)))
    (((quote _.0)
      (_.1 _.2)
      ((_.3 . _.4) (_.5 . _.6))
      (application-inner-k
       (closure _.7 _.8 ((_.8 . _.9) (_.3 . _.10)))
       (empty-k)
       _.11)
      _.5)
     (=/= ((_.7 _.8)))
     (num _.3)
     (sym _.7 _.8)
     (absento (closure _.0) (quote _.1)))
    (((quote _.0)
      (_.1 _.2)
      ((_.3 _.4 . _.5) (_.6 _.7 . _.8))
      (application-inner-k
       (closure _.9 _.10 ((_.11 _.10 . _.12) (_.13 _.14 . _.15)))
       (empty-k)
       _.16)
      _.0)
     (=/= ((_.10 _.11)) ((_.10 _.9)) ((_.14 _.3)) ((_.14 _.4)))
     (num _.13 _.14 _.3 _.4)
     (sym _.10 _.11 _.9)
     (absento (_.14 _.5) (closure _.0) (quote _.1)))))

(test "cesk-empty-list-backwards"
  (run 8 (q)
    (fresh (expr k datum x y env^ env store val v-out)
      (== '(list) expr)
      (=/= empty-k k)
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
      (application-inner-k
       (closure _.4 '_.5 (_.6 _.7))
       (empty-k)
       _.8)
      _.5)
     (=/= ((_.4 quote)))
     (sym _.4)
     (absento (closure _.5) (list _.0) '_.6))
    (((list)
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k
       (closure _.4 (lambda (_.5) _.6) (_.7 _.8))
       (empty-k)
       _.9)
      (closure _.5 _.6 ((_.4 . _.7) (_.10 . _.8))))
     (=/= ((_.4 lambda)))
     (num _.10)
     (sym _.4 _.5)
     (absento (_.10 _.2) (lambda _.7) (list _.0)))
    (((list)
      (_.0 _.1)
      _.2
      (list-aux-outer-k (_.3) _.4 (empty-k) _.5)
      (()))
     (absento (list _.0)))
    (((list)
      (_.0 _.1)
      _.2
      (list-aux-inner-k _.3 (list-aux-inner-k _.4 (empty-k)))
      (_.4 _.3))
     (absento (list _.0)))
    (((list)
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k
       (closure _.4 '_.5 (_.6 _.7))
       (list-aux-inner-k _.8 (empty-k))
       _.9)
      (_.8 . _.5))
     (=/= ((_.4 quote)))
     (sym _.4)
     (absento (closure _.5) (list _.0) '_.6))
    (((list)
      (_.0 _.1)
      (_.2 _.3)
      (list-aux-inner-k
       _.4
       (application-inner-k
        (closure _.5 '_.6 (_.7 _.8))
        (empty-k)
        _.9))
      _.6)
     (=/= ((_.5 quote)))
     (sym _.5)
     (absento (closure _.6) (list _.0) '_.7))
    (((list)
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k
       (closure _.4 '_.5 (_.6 _.7))
       (application-inner-k
        (closure _.8 '_.9 (_.10 _.11))
        (empty-k)
        _.12)
       _.13)
      _.9)
     (=/= ((_.4 quote)) ((_.8 quote)))
     (sym _.4 _.8)
     (absento (closure _.5) (closure _.9) (list _.0) '_.10
              '_.6))))

(test "cesk-nested-lists"
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
  '((((list (list))
      (_.0 _.1)
      _.2
      (empty-k)
      (()))
     (absento (list _.0)))
    (((list (list))
      (_.0 _.1)
      _.2
      (list-aux-inner-k _.3 (empty-k))
      (_.3 ()))
     (absento (list _.0)))
    (((list (list))
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k
       (closure _.4 '(_.5 . _.6) (_.7 _.8))
       (empty-k)
       _.9)
      (_.5 . _.6))
     (=/= ((_.4 quote)))
     (sym _.4)
     (absento (closure _.5) (closure _.6) (list _.0) '_.7))
    (((list (list))
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k
       (closure _.4 (lambda (_.5) _.6) (_.7 _.8))
       (empty-k)
       _.9)
      (closure _.5 _.6 ((_.4 . _.7) (_.10 . _.8))))
     (=/= ((_.4 lambda)))
     (num _.10)
     (sym _.4 _.5)
     (absento (_.10 _.2) (lambda _.7) (list _.0)))))

(test "cesk-empty-list-application"
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
      (application-inner-k
       (closure _.4 '_.5 (_.6 _.7))
       (empty-k)
       _.8)
      _.5)
     (=/= ((_.4 quote)))
     (sym _.4)
     (absento (closure _.5) (lambda _.0) (list _.0) '_.0 '_.6))
    ((((lambda (x) '(foo bar)) (list))
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k
       (closure _.4 (lambda (_.5) _.6) (_.7 _.8))
       (empty-k)
       _.9)
      (closure _.5 _.6 ((_.4 . _.7) (_.10 . _.8))))
     (=/= ((_.4 lambda)))
     (num _.10)
     (sym _.4 _.5)
     (absento (_.10 _.2) (lambda _.0) (lambda _.7) (list _.0)
              '_.0))))

(test "cesk-empty-list-non-empty-answer-backwards-1"
  (run 1 (q)
    (fresh (expr k datum x y env^ env store val v-out)
      (== '(list) expr)
      (==
       `(application-inner-k
         (closure ,x (quote foo) ,env^)
         (empty-k)
         ,v-out)
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
      (application-inner-k (closure _.4 'foo (_.5 _.6)) (empty-k) _.7)
      foo)
     (=/= ((_.4 quote)))
     (sym _.4)
     (absento (list _.0) '_.5))))

(test "cesk-empty-list-non-empty-answer-backwards-2"
  (run 4 (q)
    (fresh (expr k datum x y env^ env store val v-out a d)
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
      (application-inner-k
       (closure _.4 '_.5 (_.6 _.7))
       (empty-k)
       _.8)
      _.5)
     (=/= ((_.4 quote)) ((_.5 ())))
     (sym _.4)
     (absento (closure _.5) (list _.0) '_.6))
    (((list)
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k
       (closure _.4 (lambda (_.5) _.6) (_.7 _.8))
       (empty-k)
       _.9)
      (closure _.5 _.6 ((_.4 . _.7) (_.10 . _.8))))
     (=/= ((_.4 lambda)))
     (num _.10)
     (sym _.4 _.5)
     (absento (_.10 _.2) (lambda _.7) (list _.0)))
    (((list)
      (_.0 _.1)
      _.2
      (list-aux-outer-k (_.3) _.4 (empty-k) _.5)
      (()))
     (absento (list _.0)))))

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
  '((('_.0
      (_.1 _.2) _.3 (empty-k) _.0)
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
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (empty-k)
       _.9)
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
       (empty-k)
       _.10)
      (closure _.6 _.7 ((_.5 . _.8) (_.11 . _.9))))
     (=/= ((_.5 lambda)))
     (num _.11)
     (sym _.5 _.6)
     (absento (_.11 _.3) (closure _.0) (lambda _.8) '_.1))
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
      (application-inner-k
       (closure _.6 '_.7 (_.8 _.9))
       (empty-k)
       _.10)
      _.7)
     (=/= ((_.6 quote)))
     (sym _.0 _.6)
     (absento (closure _.7) (lambda _.2) '_.8))
    (('_.0
      (_.1 _.2)
      _.3
      (list-aux-outer-k (_.4) _.5 (empty-k) _.6)
      (_.0))
     (absento (closure _.0) '_.1))
    (((list) (_.0 _.1) _.2 (empty-k) ()) (absento (list _.0)))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.2 . _.5) (_.6 _.7 . _.8))
          (empty-k)
          _.7)
     (=/= ((_.2 _.4)))
     (num _.2 _.4)
     (sym _.0))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (list-aux-inner-k _.9 (empty-k))
       _.10)
      (_.9 . _.6))
     (=/= ((_.5 quote)))
     (sym _.5)
     (absento (closure _.0) (closure _.6) '_.1 '_.7))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 (lambda (_.7) _.8) (_.9 _.10))
       (empty-k)
       _.11)
      (closure _.7 _.8 ((_.6 . _.9) (_.12 . _.10))))
     (=/= ((_.6 lambda)))
     (num _.12)
     (sym _.0 _.6 _.7)
     (absento (_.12 _.4) (lambda _.2) (lambda _.9)))
    (('_.0
      (_.1 _.2)
      _.3
      (list-aux-inner-k _.4 (list-aux-inner-k _.5 (empty-k)))
      (_.5 _.4 . _.0))
     (absento (closure _.0) '_.1))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (list-aux-inner-k
       _.5
       (application-inner-k
        (closure _.6 '_.7 (_.8 _.9))
        (empty-k)
        _.10))
      _.7)
     (=/= ((_.6 quote)))
     (sym _.6)
     (absento (closure _.0) (closure _.7) '_.1 '_.8))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (application-inner-k
        (closure _.9 '_.10 (_.11 _.12))
        (empty-k)
        _.13)
       _.14)
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
      (application-inner-k
       (closure _.5 _.5 (_.6 _.7))
       (empty-k)
       _.8)
      _.0)
     (sym _.5)
     (absento (closure _.0) '_.1))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 '_.7 (_.8 _.9))
       (list-aux-inner-k _.10 (empty-k))
       _.11)
      (_.10 . _.7))
     (=/= ((_.6 quote)))
     (sym _.0 _.6)
     (absento (closure _.7) (lambda _.2) '_.8))
    (('_.0
      (_.1 _.2)
      _.3
      (list-aux-outer-k
       (_.4)
       _.5
       (list-aux-inner-k _.6 (empty-k))
       _.7)
      (_.6 _.0))
     (absento (closure _.0) '_.1))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (list-aux-inner-k
       _.5
       (application-inner-k
        (closure _.6 (lambda (_.7) _.8) (_.9 _.10))
        (empty-k)
        _.11))
      (closure _.7 _.8 ((_.6 . _.9) (_.12 . _.10))))
     (=/= ((_.6 lambda)))
     (num _.12)
     (sym _.6 _.7)
     (absento (_.12 _.3) (closure _.0) (lambda _.9) '_.1))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (application-inner-k
        (closure _.9 (lambda (_.10) _.11) (_.12 _.13))
        (empty-k)
        _.14)
       _.15)
      (closure _.10 _.11 ((_.9 . _.12) (_.16 . _.13))))
     (=/= ((_.5 quote)) ((_.9 lambda)))
     (num _.16)
     (sym _.10 _.5 _.9)
     (absento (_.16 _.3) (closure _.0) (closure _.6)
              (lambda _.12) '_.1 '_.7))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (_.5 . _.6))
          (list-aux-inner-k _.7 (empty-k))
          (_.7 . _.5))
     (num _.2)
     (sym _.0))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 (lambda (_.6) _.7) (_.8 _.9))
       (list-aux-inner-k _.10 (empty-k))
       _.11)
      (_.10 closure _.6 _.7 ((_.5 . _.8) (_.12 . _.9))))
     (=/= ((_.5 lambda)))
     (num _.12)
     (sym _.5 _.6)
     (absento (_.12 _.3) (closure _.0) (lambda _.8) '_.1))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (_.5 . _.6))
          (application-inner-k
           (closure _.7 '_.8 (_.9 _.10))
           (empty-k)
           _.11)
          _.8)
     (=/= ((_.7 quote)))
     (num _.2)
     (sym _.0 _.7)
     (absento (closure _.8) '_.9))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 (lambda (_.6) _.7) (_.8 _.9))
       (application-inner-k
        (closure _.10 '_.11 (_.12 _.13))
        (empty-k)
        _.14)
       _.15)
      _.11)
     (=/= ((_.10 quote)) ((_.5 lambda)))
     (sym _.10 _.5 _.6)
     (absento (closure _.0) (closure _.11) (lambda _.8) '_.1
              '_.12))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      _.4
      (list-aux-outer-k (_.5) _.6 (empty-k) _.7)
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
        (empty-k)
        _.14)
       _.15)
      _.11)
     (=/= ((_.10 quote)) ((_.6 quote)))
     (sym _.0 _.10 _.6)
     (absento (closure _.11) (closure _.7) (lambda _.2) '_.12
              '_.8))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (list-aux-outer-k
       (_.5)
       _.6
       (application-inner-k
        (closure _.7 '_.8 (_.9 _.10))
        (empty-k)
        _.11)
       _.12)
      _.8)
     (=/= ((_.7 quote)))
     (sym _.7)
     (absento (closure _.0) (closure _.8) '_.1 '_.9))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      _.4
      (list-aux-inner-k _.5 (list-aux-inner-k _.6 (empty-k)))
      (_.6 _.5 closure _.0 _.1 (_.2 _.3)))
     (sym _.0)
     (absento (lambda _.2)))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (list-aux-outer-k (_.9) _.10 (empty-k) _.11)
       _.12)
      (_.6))
     (=/= ((_.5 quote)))
     (sym _.5)
     (absento (closure _.0) (closure _.6) '_.1 '_.7))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 (list) (_.6 _.7))
       (empty-k)
       _.8)
      ())
     (=/= ((_.5 list)))
     (sym _.5)
     (absento (closure _.0) (list _.6) '_.1))
    (((list)
      (_.0 _.1)
      _.2
      (list-aux-inner-k _.3 (empty-k))
      (_.3))
     (absento (list _.0)))
    (((lambda (_.0) '_.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-outer-k '_.6 (_.7 _.8) (empty-k) _.9)
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
       (empty-k)
       _.12)
      _.0)
     (=/= ((_.10 _.3)) ((_.7 _.8)))
     (num _.10 _.3)
     (sym _.7 _.8)
     (absento (_.10 _.4) (closure _.0) '_.1))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 _.6 (_.7 _.8))
       (empty-k)
       _.9)
      (closure _.0 _.1 (_.2 _.3)))
     (sym _.0 _.6)
     (absento (lambda _.2)))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (list-aux-inner-k
       _.5
       (application-inner-k
        (closure _.6 '_.7 (_.8 _.9))
        (list-aux-inner-k _.10 (empty-k))
        _.11))
      (_.10 . _.7))
     (=/= ((_.6 quote)))
     (sym _.6)
     (absento (closure _.0) (closure _.7) '_.1 '_.8))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (application-inner-k
        (closure _.9 '_.10 (_.11 _.12))
        (list-aux-inner-k _.13 (empty-k))
        _.14)
       _.15)
      (_.13 . _.10))
     (=/= ((_.5 quote)) ((_.9 quote)))
     (sym _.5 _.9)
     (absento (closure _.0) (closure _.10) (closure _.6) '_.1
              '_.11 '_.7))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (_.5 . _.6))
          (application-inner-k
           (closure _.7 (lambda (_.8) _.9) (_.10 _.11))
           (empty-k)
           _.12)
          (closure _.8 _.9 ((_.7 . _.10) (_.13 . _.11))))
     (=/= ((_.13 _.2)) ((_.7 lambda)))
     (num _.13 _.2)
     (sym _.0 _.7 _.8)
     (absento (_.13 _.4) (lambda _.10)))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 (lambda (_.6) _.7) (_.8 _.9))
       (application-inner-k
        (closure _.10 (lambda (_.11) _.12) (_.13 _.14))
        (empty-k)
        _.15)
       _.16)
      (closure _.11 _.12 ((_.10 . _.13) (_.17 . _.14))))
     (=/= ((_.10 lambda)) ((_.5 lambda)))
     (num _.17)
     (sym _.10 _.11 _.5 _.6)
     (absento (_.17 _.3) (closure _.0) (lambda _.13) (lambda _.8)
              '_.1))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 '_.7 (_.8 _.9))
       (application-inner-k
        (closure _.10 (lambda (_.11) _.12) (_.13 _.14))
        (empty-k)
        _.15)
       _.16)
      (closure _.11 _.12 ((_.10 . _.13) (_.17 . _.14))))
     (=/= ((_.10 lambda)) ((_.6 quote)))
     (num _.17)
     (sym _.0 _.10 _.11 _.6)
     (absento (_.17 _.4) (closure _.7) (lambda _.13) (lambda _.2)
              '_.8))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (list-aux-outer-k
       (_.5)
       _.6
       (application-inner-k
        (closure _.7 (lambda (_.8) _.9) (_.10 _.11))
        (empty-k)
        _.12)
       _.13)
      (closure _.8 _.9 ((_.7 . _.10) (_.14 . _.11))))
     (=/= ((_.7 lambda)))
     (num _.14)
     (sym _.7 _.8)
     (absento (_.14 _.3) (closure _.0) (lambda _.10) '_.1))
    (((lambda (_.0) (lambda (_.1) _.2))
      (_.3 _.4)
      (_.5 _.6)
      (application-outer-k '_.7 (_.8 _.9) (empty-k) _.10)
      (closure _.1 _.2 ((_.0 . _.3) (_.11 . _.4))))
     (=/= ((_.0 lambda)))
     (num _.11)
     (sym _.0 _.1)
     (absento (_.11 _.5) (closure _.7) (lambda _.3) '_.8))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.2 . _.5) (_.6 _.7 . _.8))
          (list-aux-inner-k _.9 (empty-k))
          (_.9 . _.7))
     (=/= ((_.2 _.4)))
     (num _.2 _.4)
     (sym _.0))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.6 (_.7 _.8))
       (list-aux-inner-k _.9 (list-aux-inner-k _.10 (empty-k)))
       _.11)
      (_.10 _.9 . _.6))
     (=/= ((_.5 quote)))
     (sym _.5)
     (absento (closure _.0) (closure _.6) '_.1 '_.7))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (list-aux-inner-k
       _.6
       (application-inner-k
        (closure _.7 '_.8 (_.9 _.10))
        (empty-k)
        _.11))
      _.8)
     (=/= ((_.7 quote)))
     (sym _.0 _.7)
     (absento (closure _.8) (lambda _.2) '_.9))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 (lambda (_.7) _.8) (_.9 _.10))
       (list-aux-inner-k _.11 (empty-k))
       _.12)
      (_.11 closure _.7 _.8 ((_.6 . _.9) (_.13 . _.10))))
     (=/= ((_.6 lambda)))
     (num _.13)
     (sym _.0 _.6 _.7)
     (absento (_.13 _.4) (lambda _.2) (lambda _.9)))
    (((list)
      (_.0 _.1)
      (_.2 _.3)
      (application-inner-k
       (closure _.4 '_.5 (_.6 _.7))
       (empty-k)
       _.8)
      _.5)
     (=/= ((_.4 quote)))
     (sym _.4)
     (absento (closure _.5) (list _.0) '_.6))
    (('_.0
      (_.1 _.2)
      _.3
      (list-aux-outer-k
       (_.4 '_.5)
       (_.6 _.7)
       (empty-k)
       (_.8 . _.9))
      (_.0 _.5))
     (absento (closure _.0) (closure _.5) '_.1 '_.6))))

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
    (((lambda (_.0)
        '((lambda (x) (list x (list 'quote x)))
          '(lambda (x) (list x (list 'quote x)))))
      '_.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1)))
    (list
     '(lambda (x) (list x (list 'quote x)))
     ''(lambda (x) (list x (list 'quote x))))
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
        ((lambda (_.1)
           '((lambda (x) (list x (list 'quote x)))
             '(lambda (x) (list x (list 'quote x)))))
         '_.2))
      '_.3)
     (=/= ((_.0 lambda)) ((_.0 quote)) ((_.1 quote)))
     (sym _.0 _.1)
     (absento (closure _.2) (closure _.3)))
    ((list
      '(lambda (x) (list x (list 'quote x)))
      ((lambda (_.0) ''(lambda (x) (list x (list 'quote x))))
       '_.1))
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1)))
    (list
     '(lambda (x) (list x (list 'quote x)))
     (list 'quote '(lambda (x) (list x (list 'quote x)))))
    (((lambda (_.0)
        (list
         '(lambda (x) (list x (list 'quote x)))
         ''(lambda (x) (list x (list 'quote x)))))
      '_.1)
     (=/= ((_.0 list)) ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1)))))

(test "cesk-fresh-bkwards"
  (run 10 (q)
    (fresh (expr v)
      (evalo expr v)
      (== `(,expr ,v) q)))
  '((('_.0 _.0) (absento (closure _.0)))
    (((lambda (_.0) _.1) (closure _.0 _.1 (() ()))) (sym _.0))
    ((list) ()) (((list '_.0) (_.0)) (absento (closure _.0)))
    (((list (lambda (_.0) _.1)) ((closure _.0 _.1 (() ()))))
     (sym _.0))
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
    (((list '_.0 '_.1) (_.0 _.1))
     (absento (closure _.0) (closure _.1)))
    ((((lambda (_.0) '_.1) (lambda (_.2) _.3)) _.1)
     (=/= ((_.0 quote)))
     (sym _.0 _.2)
     (absento (closure _.1)))
    ((((lambda (_.0) _.0) '_.1) _.1)
     (sym _.0)
     (absento (closure _.1)))))

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
        (list _.0 ((lambda (_.1) (list 'quote _.0)) '_.2)))
      '(lambda (_.0)
         (list _.0 ((lambda (_.1) (list 'quote _.0)) '_.2))))
     (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
          ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
     (sym _.0 _.1)
     (absento (closure _.2)))))


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

