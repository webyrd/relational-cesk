(ns cesk.bang
  (:use [cesk.utils])
  (:use [cesk.lookupo])
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom]))

(defmacro in-new-package [[p] & body]
  `(nom/fresh [closure-nom# void-nom#]
     (let [~p [closure-nom# void-nom#]] ~@body)))
(defn closure-nom [[c v]] c)
(defn void-nom [[c v]] v)

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

(defn throw-k
  [v-e env]
  `(~'throw-k ~v-e ~env))

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

(defn set-k
  [x env k]
  `(~'set-k ~x ~env ~k))

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
    [(fresh [x addr env k v s= s== v-out-ignore]
       (nomo addr)
       (== (set-k x env k) k=)
       (== (answer v s=) v_s)
       (ext-storeo addr v s= s==)
       (lookup-env-only-auxo x env addr)
       (apply-ko p k (answer (void-nom p) s==) out v-out-ignore)
         )]
    [(fresh [v-e env= cc s v-out-ignore]
         (== (throw-k v-e env=) k=)
         (== (answer cc s) v_s)
         (eval-exp-auxo p v-e env= s cc out v-out-ignore))]
    [(fresh [r k a s== v-out=]
       (== (application-inner-k r k v-out=) k=)
       (== (answer a s==) v_s)
       (apply-proco p r a s== k out v-out=) ; v-out
       )]
    [(fresh [rand env k r s= v-out= v-out-ignore]
       (== (application-outer-k rand env k v-out=) k=)
       (== (answer r s=) v_s)

;;; this is actually incorrect!
;;; causes failure too quickly--test  letcc/throw-2c fails if this
;;; code is included.
;;; this isn't related to v-out, but p had better be a closure
       ;; (fresh [x body env=]
       ;;   (== (make-proc p x body env=) r))

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
       (nom/hash (void-nom p) datum)
       (== datum v-out) ; v-out
       (apply-ko p k (answer datum s) out v-out))]
    [(fresh [body]
       (nom/fresh [x]
         (== `(~'fn ~(nom/tie x body)) exp)
         (== (make-proc p x body env) v-out) ; v-out
         (apply-ko p k (answer (make-proc p x body env) s) out v-out)))]
    [(fresh [body env= s= v-out-ignore]
       (nom/fresh [cc addr]
         (== `(~'letcc ~(nom/tie cc body)) exp)
         (not-in-storeo addr s)
         (ext-envo cc addr env env=)
         (ext-storeo addr k s s=)
         (eval-exp-auxo p body env= s= k out v-out-ignore)))]    
    [(fresh [v]
       (nomo exp)
       (== v v-out) ; v-out
       (lookupo exp env s v)
       (apply-ko p k (answer v s) out v-out))]
    [(fresh [x e v-out-ignore]
       (== `(~'set ~x ~e) exp)
       (nomo x)
       ;; (== (void-nom p) v-out) ; v-out
       (eval-exp-auxo p e env s (set-k x env k) out v-out-ignore))]
    [(fresh [cc-e v-e v-out-ignore]
       (== `(~'throw ~cc-e ~v-e) exp)
       (eval-exp-auxo p cc-e env s (throw-k v-e env) out v-out-ignore))]
    [(fresh [rator rand v-out-ignore]
       (== `(~rator ~rand) exp)
       (eval-exp-auxo p rator env s (application-outer-k rand env k v-out) out v-out-ignore) ; v-out
       )]
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
  (in-new-package [p]
    ((evalpo p) exp out)))
