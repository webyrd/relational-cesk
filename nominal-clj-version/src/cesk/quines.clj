(ns cesk.quines
  (:use [cesk.utils])
  (:use [cesk.lookupo])
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom]))

(defmacro in-new-package [[p] & body]
  `(nom/fresh [~p]
     ~@body))
(defn closure-nom [p] p)

(defn answer [x y] [x y])

(defn not-in-envo
;;; with the old absento, this definition only works if x is a ground symbol
  [x env]
  (fresh [x*]
    (nomo x)
    (env->x*o env x*)
    (nom/hash x x*)))

(defn not-in-storeo
  [addr store]
  (fresh [addr*]
    (nomo addr)
    (store->addr*o store addr*)
    (nom/hash addr addr*)))

(defn make-proc
  [p x body env]
  `(~(closure-nom p) ~x ~body ~env))

(def empty-k '(empty-k))

(defn application-inner-k
  [p k v-out=]
  `(~'application-inner-k ~p ~k ~v-out=))

(defn application-outer-k
  [rand env k v-out=]
  `(~'application-outer-k ~rand ~env ~k ~v-out=))

(defn list-aux-inner-k
  [v k]
  `(~'list-aux-inner-k ~v ~k))

(defn list-aux-outer-k
  [e* env k v-out=]
  `(~'list-aux-outer-k ~e* ~env ~k ~v-out=))

(declare eval-exp-auxo)
(defn apply-proco
  [p r a s= k= out v-out]
  (fresh [x body env env= s==]
    (nom/fresh [addr]
      (== (make-proc p x body env) r)
      (not-in-storeo addr s=)
      (ext-envo x addr env env=)
      (ext-storeo addr a s= s==)
      (eval-exp-auxo p body env= s== k= out v-out)) ; v-out
    ))

(declare list-auxo)
(defn apply-ko
  [p k= v_s out v-out]
  (conde
    [(fresh [v s]
       (== empty-k k=)
       (== v_s out)
       (== (lcons v s) v_s)
       (== v v-out)) ; v-out
      ]
    [(fresh [r k a s== v-out=]
       (== (application-inner-k r k v-out=) k=)
       (== (answer a s==) v_s)
       (apply-proco p r a s== k out v-out=) ; v-out
       )]
    [(fresh [rand env k r s= v-out= v-out-ignore]
       (== (application-outer-k rand env k v-out=) k=)
       (== (answer r s=) v_s)

                                        ; this isn't related to v-out, but p had better be a closure
;;; ** this fail-fast optimization is unsound in the presence of
;;; letcc/throw or call/cc! **
       (fresh [x body env=]
         (== (make-proc p x body env=) r))

       (eval-exp-auxo p rand env s= (application-inner-k r k v-out=) out v-out-ignore) ; v-out
       )]
    [(fresh [v k v* s== v-out-ignore]
       (== (list-aux-inner-k v k) k=)
       (== (answer v* s==) v_s)
       (== v* v-out) ; v-out
       (apply-ko p k (answer (lcons v v*) s==) out v-out-ignore))]
    [(fresh [e* env k v s= e*-rest ignore v-out-rest]
       (== (list-aux-outer-k e* env k v-out-rest) k=)
       (== (answer v s=) v_s)
       (== (lcons ignore e*-rest) e*)
       (list-auxo p e*-rest env s= (list-aux-inner-k v k) out v-out-rest))]))

(defn eval-exp-auxo
  [p exp env s k out v-out]
  (conde
    [(fresh [datum]
       (== `(~'quote ~datum) exp)
       (nom/hash (closure-nom p) datum)
       (== datum v-out) ; v-out
       (apply-ko p k (answer datum s) out v-out))]
    [(fresh [v]
       (nomo exp)
       (== v v-out) ; v-out
       (lookupo exp env s v)
       (apply-ko p k (answer v s) out v-out))]
    [(fresh [rator rand v-out-ignore]
       (== `(~rator ~rand) exp)
       (eval-exp-auxo p rator env s (application-outer-k rand env k v-out) out v-out-ignore) ; v-out
       )]
    [(fresh [body]
       (nom/fresh [x]
         (== (nom/tie x body) exp)
         (== (make-proc p x body env) v-out) ; v-out
         (apply-ko p k (answer (make-proc p x body env) s) out v-out)))]
    [(fresh [e*]
       (== (lcons 'list e*) exp)
       (list-auxo p e* env s k out v-out) ; v-out
       )]))

(defn list-auxo
  [p e* env s k out v-out*]
  (conde
    [(fresh [v-out-ignore]
       (== '() e*)
       (== '() v-out*) ; v-out*
       (apply-ko p k (answer '() s) out v-out-ignore))]
    [(fresh [e ignore v-out v-out-rest]
       (== (lcons e ignore) e*)
       (== (lcons v-out v-out-rest) v-out*) ; v-out*
       (eval-exp-auxo p e env s (list-aux-outer-k e* env k v-out-rest) out v-out))]))

(defn eval-expo
  [p exp env s k out]
  (fresh [ans v s=]
    (== (answer v s=) ans)
    (== out v)
    (eval-exp-auxo p exp env s k ans v)))

(defn evalpo [p]
  (fn [exp out]
    (eval-expo p exp empty-env empty-store empty-k out)))
(defn evalo
  [exp out]
  (fresh [p]
    (in-new-package [p]
      ((evalpo p) exp out))))

