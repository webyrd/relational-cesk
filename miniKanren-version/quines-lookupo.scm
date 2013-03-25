(load "mk.scm")
(load "test-check.scm")

;;; Modified 'improved lookupo' code, using symbolo for variables and
;;; numbero for addresses.

(define empty-env '(() ()))
(define empty-store '(() ()))

(define ext-envo
  (lambda (x addr env env^)
    (fresh (x* addr*)
      (== `(,x* ,addr*) env)
      (== `((,x . ,x*) (,addr . ,addr*)) env^)
      (symbolo x)
      (numbero addr))))

(define ext-storeo
  (lambda (addr v store store^)
    (fresh (addr* v*)
      (== `(,addr* ,v*) store)
      (== `((,addr . ,addr*) (,v . ,v*)) store^)
      (numbero addr))))

(define x*/addr*-envo
  (lambda (x* a* env)
    (== `(,x* ,a*) env)))

(define addr*/val*-storeo
  (lambda (a* v* store)
    (== `(,a* ,v*) store)))

(define env->x*o
  (lambda (env x*)
    (fresh (a*)
      (== `(,x* ,a*) env))))

(define env->addr*o
  (lambda (env a*)
    (fresh (x*)
      (== `(,x* ,a*) env))))

(define store->addr*o
  (lambda (store a*)
    (fresh (v*)
      (== `(,a* ,v*) store))))

(define store->val*o
  (lambda (store v*)
    (fresh (a*)
      (== `(,a* ,v*) store))))




(define lookupo
  (lambda (x env store t)
    (fresh (addr)
      (symbolo x)
      (numbero addr)
      (lookup-env-auxo x env store addr)
      (lookup-store-auxo addr store t))))

(define lookup-env-auxo
;;; it may be possible to avoid having to bound the length of env to
;;; be no greater than the length of store through clever use of
;;; noo/absento.  For now, however, we'll stick with the bound.
  (lambda (x env store t)
    (fresh (y y* addr-e addr-e* addr-s addr-s* v-s v-s*)      
      (== `((,y . ,y*) (,addr-e . ,addr-e*)) env)
      (== `((,addr-s . ,addr-s*) (,v-s . ,v-s*)) store)
      (symbolo x)
      (symbolo y)
      (numbero t)
      (numbero addr-e)
      (numbero addr-s)
      (conde
        ((== y x) (== addr-e t))
        ((=/= y x)
         (lookup-env-auxo x `(,y* ,addr-e*) `(,addr-s* ,v-s*) t))))))

(define lookup-env-only-auxo
  (lambda (x env t)
    (fresh (y y* addr-e addr-e*)
      (== `((,y . ,y*) (,addr-e . ,addr-e*)) env)
      (symbolo x)
      (symbolo y)
      (numbero t)
      (numbero addr-e)
      (conde
        ((== y x) (== addr-e t))
        ((=/= y x)
         (lookup-env-only-auxo x `(,y* ,addr-e*) t))))))

(define lookup-store-auxo
  (lambda (addr store t)
    (fresh (addr-s addr-s* v-s v-s*)
      (== `((,addr-s . ,addr-s*) (,v-s . ,v-s*)) store)
      (numbero addr)
      (numbero addr-s)
      (conde
        ((== addr-s addr) (== v-s t))
        ((=/= addr-s addr)
         (lookup-store-auxo addr `(,addr-s* ,v-s*) t))))))

(test "improved-lookupo-0"
  (run 1 (q) (lookupo 'x '(() ()) '(() ()) q))
  '())

(test "improved-lookupo-1"
  (run 1 (q) (lookupo 'x '((w x y) (0 1 2)) '((0 1 2) (foo bar baz)) q))
  '(bar))

(test "improved-lookupo-2"
  (run 2 (q) (lookupo 'x '((w x y) (0 1 2)) '((0 1 2) (foo bar baz)) q))
  '(bar))

(test "improved-lookupo-3"
  (run* (q) (lookupo 'x '((w x y) (0 1 2)) '((0 1 2) (foo bar baz)) q))  
  '(bar))

(test "improved-lookupo-4"
  (run 10 (q)
    (fresh (id env store val)
      (lookupo id env store val)
      (== `(,id ,env ,store ,val) q)))
  '(((_.0
      ((_.0 . _.1) (_.2 . _.3))
      ((_.2 . _.4) (_.5 . _.6))
      _.5)
     (num _.2)
     (sym _.0))
    ((_.0
      ((_.0 . _.1) (_.2 . _.3))
      ((_.4 _.2 . _.5) (_.6 _.7 . _.8))
      _.7)
     (=/= ((_.2 _.4)))
     (num _.2 _.4)
     (sym _.0))
    ((_.0
      ((_.1 _.0 . _.2) (_.3 _.4 . _.5))
      ((_.4 _.6 . _.7) (_.8 _.9 . _.10))
      _.8)
     (=/= ((_.0 _.1)))
     (num _.3 _.4 _.6)
     (sym _.0 _.1))
    ((_.0
      ((_.0 . _.1) (_.2 . _.3))
      ((_.4 _.5 _.2 . _.6) (_.7 _.8 _.9 . _.10))
      _.9)
     (=/= ((_.2 _.4)) ((_.2 _.5)))
     (num _.2 _.4 _.5)
     (sym _.0))
    ((_.0
      ((_.0 . _.1) (_.2 . _.3))
      ((_.4 _.5 _.6 _.2 . _.7) (_.8 _.9 _.10 _.11 . _.12))
      _.11)
     (=/= ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)))
     (num _.2 _.4 _.5 _.6)
     (sym _.0))
    ((_.0
      ((_.1 _.0 . _.2) (_.3 _.4 . _.5))
      ((_.6 _.4 . _.7) (_.8 _.9 . _.10))
      _.9)
     (=/= ((_.0 _.1)) ((_.4 _.6)))
     (num _.3 _.4 _.6)
     (sym _.0 _.1))
    ((_.0
      ((_.0 . _.1) (_.2 . _.3))
      ((_.4 _.5 _.6 _.7 _.2 . _.8)
       (_.9 _.10 _.11 _.12 _.13 . _.14))
      _.13)
     (=/= ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)) ((_.2 _.7)))
     (num _.2 _.4 _.5 _.6 _.7)
     (sym _.0))
    ((_.0
      ((_.1 _.2 _.0 . _.3) (_.4 _.5 _.6 . _.7))
      ((_.6 _.8 _.9 . _.10) (_.11 _.12 _.13 . _.14))
      _.11)
     (=/= ((_.0 _.1)) ((_.0 _.2)))
     (num _.4 _.5 _.6 _.8 _.9)
     (sym _.0 _.1 _.2))
    ((_.0
      ((_.0 . _.1) (_.2 . _.3))
      ((_.4 _.5 _.6 _.7 _.8 _.2 . _.9)
       (_.10 _.11 _.12 _.13 _.14 _.15 . _.16))
      _.15)
     (=/= ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)) ((_.2 _.7)) ((_.2 _.8)))
     (num _.2 _.4 _.5 _.6 _.7 _.8)
     (sym _.0))
    ((_.0
      ((_.1 _.0 . _.2) (_.3 _.4 . _.5))
      ((_.6 _.7 _.4 . _.8) (_.9 _.10 _.11 . _.12))
      _.11)
     (=/= ((_.0 _.1)) ((_.4 _.6)) ((_.4 _.7)))
     (num _.3 _.4 _.6 _.7)
     (sym _.0 _.1))))

(test "improved-lookupo-4a"
  (run 5 (q)
    (fresh (id env store val)
      (lookupo id env store val)
      (== `(,id ,env ,store ,val) q)))
  '(((_.0
      ((_.0 . _.1) (_.2 . _.3))
      ((_.2 . _.4) (_.5 . _.6))
      _.5)
     (num _.2)
     (sym _.0))
    ((_.0
      ((_.0 . _.1) (_.2 . _.3))
      ((_.4 _.2 . _.5) (_.6 _.7 . _.8))
      _.7)
     (=/= ((_.2 _.4)))
     (num _.2 _.4)
     (sym _.0))
    ((_.0
      ((_.1 _.0 . _.2) (_.3 _.4 . _.5))
      ((_.4 _.6 . _.7) (_.8 _.9 . _.10))
      _.8)
     (=/= ((_.0 _.1)))
     (num _.3 _.4 _.6)
     (sym _.0 _.1))
    ((_.0
      ((_.0 . _.1) (_.2 . _.3))
      ((_.4 _.5 _.2 . _.6) (_.7 _.8 _.9 . _.10))
      _.9)
     (=/= ((_.2 _.4)) ((_.2 _.5)))
     (num _.2 _.4 _.5)
     (sym _.0))
    ((_.0
      ((_.0 . _.1) (_.2 . _.3))
      ((_.4 _.5 _.6 _.2 . _.7) (_.8 _.9 _.10 _.11 . _.12))
      _.11)
     (=/= ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)))
     (num _.2 _.4 _.5 _.6)
     (sym _.0))))

(test "improved-lookupo-5"
  (run 10 (q)
    (fresh (id env store val)
      (symbolo id)
      (lookupo id env store val)
      (== `(,id ,env ,store ,val) q)))
  '(((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.2 . _.4) (_.5 . _.6)) _.5) (num _.2) (sym _.0))
    ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.2 . _.5) (_.6 _.7 . _.8)) _.7) (=/= ((_.2 _.4))) (num _.2 _.4) (sym _.0))
    ((_.0 ((_.1 _.0 . _.2) (_.3 _.4 . _.5)) ((_.4 _.6 . _.7) (_.8 _.9 . _.10)) _.8) (=/= ((_.0 _.1))) (num _.3 _.4 _.6) (sym _.0 _.1))
    ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.5 _.2 . _.6) (_.7 _.8 _.9 . _.10)) _.9) (=/= ((_.2 _.4)) ((_.2 _.5))) (num _.2 _.4 _.5) (sym _.0))
    ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.5 _.6 _.2 . _.7) (_.8 _.9 _.10 _.11 . _.12)) _.11) (=/= ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6))) (num _.2 _.4 _.5 _.6) (sym _.0))
    ((_.0 ((_.1 _.0 . _.2) (_.3 _.4 . _.5)) ((_.6 _.4 . _.7) (_.8 _.9 . _.10)) _.9) (=/= ((_.0 _.1)) ((_.4 _.6))) (num _.3 _.4 _.6) (sym _.0 _.1))
    ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.5 _.6 _.7 _.2 . _.8) (_.9 _.10 _.11 _.12 _.13 . _.14)) _.13) (=/= ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)) ((_.2 _.7))) (num _.2 _.4 _.5 _.6 _.7) (sym _.0))
    ((_.0 ((_.1 _.2 _.0 . _.3) (_.4 _.5 _.6 . _.7)) ((_.6 _.8 _.9 . _.10) (_.11 _.12 _.13 . _.14)) _.11) (=/= ((_.0 _.1)) ((_.0 _.2))) (num _.4 _.5 _.6 _.8 _.9) (sym _.0 _.1 _.2))
    ((_.0 ((_.0 . _.1) (_.2 . _.3)) ((_.4 _.5 _.6 _.7 _.8 _.2 . _.9) (_.10 _.11 _.12 _.13 _.14 _.15 . _.16)) _.15) (=/= ((_.2 _.4)) ((_.2 _.5)) ((_.2 _.6)) ((_.2 _.7)) ((_.2 _.8))) (num _.2 _.4 _.5 _.6 _.7 _.8) (sym _.0))
    ((_.0 ((_.1 _.0 . _.2) (_.3 _.4 . _.5)) ((_.6 _.7 _.4 . _.8) (_.9 _.10 _.11 . _.12)) _.11) (=/= ((_.0 _.1)) ((_.4 _.6)) ((_.4 _.7))) (num _.3 _.4 _.6 _.7) (sym _.0 _.1))))

(test "improved-lookupo-6"
  (run 1 (q) (lookupo q '((w x y) (0 1 2)) '((0 1 2) (foo bar baz)) 'foo))
  '(w))

(test "improved-lookupo-7"
  (run 2 (q) (lookupo q '((w x y) (0 1 2)) '((0 1 2) (foo bar baz)) 'foo))
  '(w))

(test "improved-lookupo-8"
  (run 1 (q) (lookupo q '((w x y) (0 1 2)) '((0 1 2) (foo bar baz)) 'quux))
  '())

(test "improved-lookupo-9"
  (run 1 (q) (lookupo 'x '((w y) (0 2)) '((0 1 2) (foo bar baz)) q))
  '())

(test "improved-lookupo-10"
  (run 1 (q) (lookupo 'x '((w x y) (0 1 2)) '((0 2) (foo baz)) q))
  '())

(test "improved-lookupo-11"
  (run 5 (q) (lookupo 'x '((w x y) (0 1 2)) q 'bar))
  '((((1 _.0 . _.1)
      (bar _.2 . _.3))
     (num _.0))
    (((_.0 1 . _.1) (_.2 bar . _.3))
     (=/= ((_.0 1)))
     (num _.0))
    (((_.0 _.1 1 . _.2)
      (_.3 _.4 bar . _.5))
     (=/= ((_.0 1)) ((_.1 1)))
     (num _.0 _.1))
    (((_.0 _.1 _.2 1 . _.3)
      (_.4 _.5 _.6 bar . _.7))
     (=/= ((_.0 1)) ((_.1 1)) ((_.2 1)))
     (num _.0 _.1 _.2))
    (((_.0 _.1 _.2 _.3 1 . _.4)
      (_.5 _.6 _.7 _.8 bar . _.9))
     (=/= ((_.0 1)) ((_.1 1)) ((_.2 1)) ((_.3 1)))
     (num _.0 _.1 _.2 _.3))))

(test "improved-lookupo-12"
  (run 1 (q)
    (fresh (addr* val*)
      (lookupo 'x '((w x y) (0 1 2)) `((1 . ,addr*) (foo . ,val*)) 'baz)
      (== `(,addr* val*) q)))
  '())

(test "improved-lookupo-12a"
  (run 5 (q)
    (fresh (addr* val*)
      (lookupo 'x '((w x y) (0 1 2)) `(,addr* ,val*) 'baz)
      (== `(,addr* ,val*) q)))
  '((((1 _.0 . _.1) (baz _.2 . _.3)) (num _.0))
    (((_.0 1 . _.1) (_.2 baz . _.3)) (=/= ((_.0 1))) (num _.0))
    (((_.0 _.1 1 . _.2) (_.3 _.4 baz . _.5))
     (=/= ((_.0 1)) ((_.1 1)))
     (num _.0 _.1))
    (((_.0 _.1 _.2 1 . _.3) (_.4 _.5 _.6 baz . _.7))
     (=/= ((_.0 1)) ((_.1 1)) ((_.2 1)))
     (num _.0 _.1 _.2))
    (((_.0 _.1 _.2 _.3 1 . _.4) (_.5 _.6 _.7 _.8 baz . _.9))
     (=/= ((_.0 1)) ((_.1 1)) ((_.2 1)) ((_.3 1)))
     (num _.0 _.1 _.2 _.3))))

(test "improved-lookupo-13"
;;; this test diverges using naive lookupo
  (run 1 (q)
    (fresh (x* addr*)
      (lookupo 'x `((w . ,x*) (0 . ,addr*)) '((1 2) (foo bar)) 'baz)
      (== `(,x* ,addr*) q)))
  '())

(test "improved-lookupo-13a"
  (run* (q)
    (fresh (x* addr*)
      (lookupo 'x `((w . ,x*) (0 . ,addr*)) '((1 2) (foo bar)) 'bar)
      (== `(,x* ,addr*) q)))
  '(((x . _.0)
     (2 . _.1))))

(test "improved-lookupo-14"
  (run 1 (q)
    (fresh (env-x* env-addr* store-addr* store-val*)
      (lookupo 'w `((w . ,env-x*) (0 . ,env-addr*))  `((0 . ,store-addr*) (foo . ,store-val*)) 'baz)
      (== `((,env-x* ,env-addr*) (,store-addr* ,store-val*)) q)))
  '())

(test "improved-lookupo-14b"
  (run 5 (q)
    (fresh (env-x* env-addr* store-addr* store-val*)
      (lookupo 'x `((w . ,env-x*) (0 . ,env-addr*))  `((0 . ,store-addr*) (foo . ,store-val*)) 'baz)
      (== `((,env-x* ,env-addr*) (,store-addr* ,store-val*)) q)))
  '(((((x . _.0) (_.1 . _.2)) ((_.1 . _.3) (baz . _.4)))
     (=/= ((_.1 0)))
     (num _.1))
    ((((x . _.0) (_.1 . _.2)) ((_.3 _.1 . _.4) (_.5 baz . _.6)))
     (=/= ((_.1 0)) ((_.1 _.3)))
     (num _.1 _.3))
    ((((x . _.0) (_.1 . _.2))
      ((_.3 _.4 _.1 . _.5) (_.6 _.7 baz . _.8)))
     (=/= ((_.1 0)) ((_.1 _.3)) ((_.1 _.4)))
     (num _.1 _.3 _.4))
    ((((_.0 x . _.1) (_.2 _.3 . _.4))
      ((_.3 _.5 . _.6) (baz _.7 . _.8)))
     (=/= ((_.0 x)) ((_.3 0)))
     (num _.2 _.3 _.5)
     (sym _.0))
    ((((x . _.0) (_.1 . _.2))
      ((_.3 _.4 _.5 _.1 . _.6) (_.7 _.8 _.9 baz . _.10)))
     (=/= ((_.1 0)) ((_.1 _.3)) ((_.1 _.4)) ((_.1 _.5)))
     (num _.1 _.3 _.4 _.5))))
