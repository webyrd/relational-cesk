(ns cesk.lookupo
  (:use [cesk.utils])
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom]))

;;; Modified 'improved lookupo' code, using symbolo for variables and
;;; numbero for addresses.

(def empty-env [() ()])
(def empty-store [() ()])

(defn ext-envo
  [x addr env env=]
  (fresh [x* addr*]
    (nomo x)
    (nomo addr)
    (== [x* addr*] env)
    (== [(lcons x x*) (lcons addr addr*)] env=)))

(defn ext-storeo
  [addr v store store=]
  (fresh [addr* v*]
    (nomo addr)
    (== [addr* v*] store)
    (== [(lcons addr addr*) (lcons v v*)] store=)))

(defn x*=addr*-envo
  [x* a* env]
  (== [x* a*] env))

(defn addr*=val*-storeo
  [a* v* store]
  (== [a* v*] store))

(defn env->x*o
  [env x*]
  (fresh [a*]
    (== [x* a*] env)))

(defn env->addr*o
  [env a*]
  (fresh [x*]
    (== [x* a*] env)))

(defn store->addr*o
  [store a*]
  (fresh [v*]
    (== [a* v*] store)))

(defn store->val*o
  [store v*]
  (fresh [a*]
    (== [a* v*] store)))



(declare lookup-env-auxo lookup-store-auxo)
(defn lookupo
  [x env store t]
  (fresh [addr]
    (nomo x)
    (nomo addr)
    (lookup-env-auxo x env store addr)
    (lookup-store-auxo addr store t)))

(defn lookup-env-auxo
;;; it may be possible to avoid having to bound the length of env to
;;; be no greater than the length of store through clever use of
;;; noo/absento.  For now, however, we'll stick with the bound.
  [x env store t]
  (fresh [y y* addr-e addr-e* addr-s addr-s* v-s v-s*]
    (nomo x)
    (nomo y)
    (nomo t)
    (nomo addr-e)
    (nomo addr-s)
    (== [(lcons y y*) (lcons addr-e addr-e*)] env)
    (== [(lcons addr-s addr-s*) (lcons v-s v-s*)] store)
    (conde
      [(== y x) (== addr-e t)]
      [(!= y x)
        (lookup-env-auxo x [y* addr-e*] [addr-s* v-s*] t)])))

(defn lookup-env-only-auxo
  [x env t]
  (fresh [y y* addr-e addr-e*]
    (nomo x)
    (nomo y)
    (nomo t)
    (nomo addr-e)
    (== [(lcons y y*) (lcons addr-e addr-e*)] env)
    (conde
      [(== y x) (== addr-e t)]
      [(!= y x)
        (lookup-env-only-auxo x [y* addr-e*] t)])))

(defn lookup-store-auxo
  [addr store t]
  (fresh [addr-s addr-s* v-s v-s*]
    (nomo addr)
    (nomo addr-s)
    (== [(lcons addr-s addr-s*) (lcons v-s v-s*)] store)
    (conde
      [(== addr-s addr) (== v-s t)]
      [(!= addr-s addr)
        (lookup-store-auxo addr [addr-s* v-s*] t)])))
