(library (cesk-scheme-callcc)
  (export evalo eval-expo empty-env empty-store empty-k)
  (import (rnrs) (mk-lib) (lookupo-lib))

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
      (eval-exp-auxo body env^ s^^ k^ out v-out) ; v-out (this use is essential--passing a fresh variable breaks ability to generate quines in a reasonable time)
      )))

(define apply-ko
  (lambda (k^ v/s out)
    (conde
      [(fresh (v s)
         (== empty-k k^)
         (== v/s out)
         (== (answer v s) v/s))
        ]
      [(fresh (x env k v s^ addr s^^)
         (== (set!-k x env k) k^)
         (== `(,v . ,s^) v/s)
         (numbero addr)
         (ext-storeo addr v s^ s^^)
         (lookup-env-only-auxo x env addr)
         (apply-ko k (answer 'void s^^) out)
         )]
      [(fresh (p k a s^^ v-out^)
         (== (application-inner-k p k v-out^) k^)
         (== (answer a s^^) v/s)
         (apply-proco p a s^^ k out v-out^) ; v-out (this use is essential--passing a fresh variable breaks ability to generate quines in a reasonable time)
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

         (eval-exp-auxo rand env s^ (application-inner-k p k v-out^) out v-out-ignore) ; v-out (this use is essential--passing a fresh variable breaks ability to generate quines in a reasonable time)
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
         (list-auxo e*-rest env s^ (list-aux-inner-k v k) out v-out-rest) ; v-out (this use is essential--passing a fresh variable breaks ability to generate quines in a reasonable time)
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

(define set!-k
  (lambda (x env k)
    `(set!-k ,x ,env ,k)))

(define eval-exp-auxo
  (lambda (exp env s k out v-out)
    (conde
      [(fresh (datum ans)
         (== `(quote ,datum) exp)
         (== datum v-out) ; v-out
         (== (answer datum s) ans)
         (fresh ()
           (absento 'closure datum)
           (absento 'void datum))
         (not-in-envo 'quote env)
         (apply-ko k ans out))]
      [(fresh (x body ans)
         (== `(lambda (,x) ,body) exp)
         (== (make-proc x body env) v-out) ; v-out
         (== (answer (make-proc x body env) s) ans)
         (not-in-envo 'lambda env)
         (symbolo x) ; interesting: adding this symbolo constraint increased the runtime by ~7%
         (apply-ko k ans out))]
      [(fresh (v ans)
         (symbolo exp)         
         (lookupo exp env s v)
         (== v v-out) ; v-out
         (== (answer v s) ans)
         (apply-ko k ans out))]
       [(fresh (x e v-out-ignore)
         (== `(set! ,x ,e) exp)
         (not-in-envo 'set! env)
         (symbolo x)
         (== 'void v-out) ; v-out
         (eval-exp-auxo e env s (set!-k x env k) out v-out-ignore))]
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
         (== '() v-out*) ; v-out*         
         (== (answer '() s) ans)
         (apply-ko k ans out))]
      [(fresh (e ignore v-out v-out^ v-out-rest v-out-e)
         (== `(,e . ,ignore) e*)
         (== `(,v-out-e . ,v-out-rest) v-out*) ; v-out*
         (eval-exp-auxo e env s (list-aux-outer-k e* env k v-out-rest) out v-out-e))])))

(define eval-expo
  (lambda (exp env s k out)
    (fresh (ans s^ v-out)
      (== (answer out s^) ans)
      (conde
        [(== empty-k k)
         (== out v-out) ; v-out
         ]
        [(=/= empty-k k)])      
      (eval-exp-auxo exp env s k ans v-out))))

(define evalo
  (lambda (exp out)
    (eval-expo exp empty-env empty-store empty-k out)))

)
