(library (lookupo-lib)
  (export empty-env empty-store ext-envo ext-storeo x*/addr*-envo addr*/val*-storeo env->x*o env->addr*o store->addr*o store->val*o lookupo lookup-env-auxo lookup-env-only-auxo lookup-store-auxo)
  (import (rnrs) (mk-lib))

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

)