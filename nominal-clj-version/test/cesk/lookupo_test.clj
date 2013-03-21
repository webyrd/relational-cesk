(ns cesk.lookupo_test
  (:use [cesk.lookupo] :reload)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom])
  (:use [clojure.test]))

(deftest improved-lookupo-0
  (is (= (run 1 (q) (nom/fresh [x] (lookupo x '(() ()) '(() ()) q)))
        '())))

(def make-proc
  (fn [x body env]
    ['closure x body env]))

(deftest improved-lookupo-1
  (is (= (run 1 (q) (nom/fresh [w x y l0 l1 l2] (lookupo x [[w x y] [l0 l1 l2]] [[l0 l1 l2] '(foo bar baz)] q)))
        '(bar))))

(deftest improved-lookupo-2
  (is (= (run 2 (q) (nom/fresh [w x y l0 l1 l2] (lookupo x [[w x y] [l0 l1 l2]] [[l0 l1 l2] '(foo bar baz)] q)))
        '(bar))))

(deftest improved-lookupo-3
  (is (= (run* (q) (nom/fresh [w x y l0 l1 l2] (lookupo x [[w x y] [l0 l1 l2]] [[l0 l1 l2] '(foo bar baz)] q)))
        '(bar))))

(deftest improved-lookupo-6
  (is (= (run 1 (q) (fresh [a] (nom/fresh [w x y l0 l1 l2]
                                 (lookupo a [[w x y] [l0 l1 l2]] [[l0 l1 l2] '(foo bar baz)] 'foo)
                                 (== q [[w x y] a]))))
        '(((a_0 a_1 a_2) a_0)))))

(deftest improved-lookupo-7
  (is (= (run* (q) (fresh [a] (nom/fresh [w x y l0 l1 l2]
                                 (lookupo a [[w x y] [l0 l1 l2]] [[l0 l1 l2] '(foo bar baz)] 'foo)
                                 (== q [[w x y] a]))))
        '(((a_0 a_1 a_2) a_0)))))

(deftest improved-lookupo-8
  (is (= (run* (q) (fresh [a] (nom/fresh [w x y l0 l1 l2]
                                 (lookupo a [[w x y] [l0 l1 l2]] [[l0 l1 l2] '(foo bar baz)] 'quux)
                                 (== q [[w x y] a]))))
        '())))

(deftest improved-lookupo-9
  (is (= (run* (q) (nom/fresh [a] (nom/fresh [w y l0 l1 l2]
                                    (lookupo a [[w y] [l0 l2]] [[l0 l1 l2] '(foo bar baz)] q))))
        '())))

(deftest improved-lookupo-10
  (is (= (run* (q) (nom/fresh [a] (nom/fresh [w x y l0 l1 l2]
                                    (lookupo a [[w x y] [l0 l1 l2]] [[l0 l2] '(foo baz)] q))))
        '())))

(deftest improved-lookupo-12
  (is (= (run 1 (q)
           (nom/fresh [w x y l0 l1 l2]
             (fresh (addr* val*)
               (lookupo x [[w x y] [l0 l1 l2]] [(lcons l1 addr*) (lcons 'foo val*)] 'baz)
               (== [addr* val*] q))))
        '())))

(deftest improved-lookupo-13
;;; this test diverges using naive lookupo
  (is (= (run 1 (q)
           (nom/fresh [w x l0 l1 l2]
             (fresh (x* addr*)
               (lookupo x [(lcons w x*) (lcons l0 addr*)] [[l1 l2] '(foo bar)] 'baz)
               (== [x* addr*] q))))
        '())))

(deftest improved-lookupo-13a
  (is (= (run* (q)
           (nom/fresh [w x l0 l1 l2]
             (fresh (x* addr*)
               (lookupo x [(lcons w x*) (lcons l0 addr*)] [[l1 l2] '(foo bar)] 'bar)
               (== [w x l0 l1 l2 [x* addr*]] q))))
        [['a_0 'a_1 'a_2 'a_3 'a_4 [(lcons 'a_1 '_5) (lcons 'a_4 '_6)]]])))

(deftest improved-lookupo-14
  (is (= (run 1 (q)
           (nom/fresh [w l0]
             (fresh (env-x* env-addr* store-addr* store-val*)
               (lookupo w [(lcons w env-x*) (lcons l0 env-addr*)] [(lcons l0 store-addr*) (lcons 'foo store-val*)] 'baz)
               (== [[env-x* env-addr*] [store-addr* store-val*]] q))))
        '())))

