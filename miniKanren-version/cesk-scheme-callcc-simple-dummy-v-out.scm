(library (cesk-scheme-callcc-simple-dummy-v-out)
  (export evalo eval-expo empty-env empty-store empty-k)
  (import (rnrs) (mk-lib) (lookupo-lib))

;;; includes dummy (fresh) slot for v-out in appropriate continuations, to make it easier to compare answers between cesk-quines.scm and cesk-quines-simple.
  
  (define answer
    (lambda (v s)
      (cons v s)))

  (define not-in-envo
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
    (lambda (p a s^ k^ out)
      (fresh (x body env addr env^ s^^)
        (== (make-proc x body env) p)
        (ext-envo x addr env env^)
        (ext-storeo addr a s^ s^^)
        (numbero addr)
        (symbolo x)
        (not-in-storeo addr s^) ; not-in-storeo also calls numbero on addr--is this redundancy desireable?
        (eval-exp-auxo body env^ s^^ k^ out)
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
        [(fresh (p k a s^^ dummy-v-out)
           (== (application-inner-k p k dummy-v-out) k^)
           (== (answer a s^^) v/s)
           (apply-proco p a s^^ k out)
           )]
        [(fresh (rand env k p s^ dummy-v-out dummy-v-out^)
           (== (application-outer-k rand env k dummy-v-out) k^)
           (== (answer p s^) v/s)
           (eval-exp-auxo rand env s^ (application-inner-k p k dummy-v-out^) out)
           )]
        [(fresh (v k v* s^^ ans)
           (== (list-aux-inner-k v k) k^)
           (== (answer v* s^^) v/s)
           (== (answer (cons v v*) s^^) ans)
           (apply-ko k ans out))]
        [(fresh (e* env k v s^ e*-rest ignore dummy-v-out)
           (== (list-aux-outer-k e* env k dummy-v-out) k^)
           (== (answer v s^) v/s)
           (== `(,ignore . ,e*-rest) e*)
           (list-auxo e*-rest env s^ (list-aux-inner-k v k) out)
           )])))

  (define empty-k '(empty-k))

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
    (lambda (exp env s k out)
      (conde
        [(fresh (datum ans)
           (== `(quote ,datum) exp)
           (== (answer datum s) ans)
           (fresh ()
             (absento 'closure datum)
             (absento 'void datum))
           (not-in-envo 'quote env)
           (apply-ko k ans out))]
        [(fresh (x body ans)
           (== `(lambda (,x) ,body) exp)
           (== (answer (make-proc x body env) s) ans)
           (not-in-envo 'lambda env)
           (symbolo x) ; interesting: adding this symbolo constraint increased the runtime by ~7%
           (apply-ko k ans out))]
        [(fresh (v ans)
           (symbolo exp)
           (== (answer v s) ans)
           (lookupo exp env s v)
           (apply-ko k ans out))]
        [(fresh (x e)
           (== `(set! ,x ,e) exp)
           (not-in-envo 'set! env)
           (symbolo x)
           ; (== 'void v-out) ; v-out
           (eval-exp-auxo e env s (set!-k x env k) out))]
        [(fresh (rator rand dummy-v-out)
           (== `(,rator ,rand) exp)
           (eval-exp-auxo rator env s (application-outer-k rand env k dummy-v-out) out)
           )]
        [(fresh (e*)
           (== `(list . ,e*) exp)
           (not-in-envo 'list env)
           (list-auxo e* env s k out)
           )])))

  (define list-auxo
    (lambda (e* env s k out)
      (conde
        [(fresh (ans)
           (== '() e*)
           (== (answer '() s) ans)
           (apply-ko k ans out))]
        [(fresh (e ignore dummy-v-out)
           (== `(,e . ,ignore) e*)
           (eval-exp-auxo e env s (list-aux-outer-k e* env k dummy-v-out) out))])))

  (define eval-expo
    (lambda (exp env s k out)
      (fresh (ans s^)
        (== (answer out s^) ans)
        (eval-exp-auxo exp env s k ans))))

  (define evalo
    (lambda (exp out)
      (eval-expo exp empty-env empty-store empty-k out)))

  )
