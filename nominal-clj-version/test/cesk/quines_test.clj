(ns cesk.quines_test
  (:use [cesk.lookupo] :reload)
  (:use [cesk.quines] :reload)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom])
  (:use [clojure.test]))

(defn to-clj [x]
  (cond
    (tie? x)
    `(~'fn [~(:binding-nom x)] ~(to-clj (:body x)))
    (and (coll? x) (not (empty? x)))
    (cons (to-clj (first x)) (to-clj (rest x)))
    :else x))

(deftest cesk-quote-a
  (is (= (to-clj (run* (q) (evalo '(quote x) q)))
        '(x))))

(deftest cesk-quote
  (is (= (to-clj (run* (q) (nom/fresh [x] (evalo `(quote ~(nom/tie x x)) q))))
        '((fn [a_0] a_0)))))

(deftest cesk-list-0
  (is (= (to-clj (run* (q) (evalo '(list) q)))
        '(()))))

(deftest cesk-closure
  (is (= (to-clj (run* (q) (nom/fresh [x] (evalo (nom/tie x x) q))))
        '((a_0 a_1 a_1 (() ()))))))

(deftest cesk-identity-a
  (is (= (to-clj (run* (q) (nom/fresh [x y] (evalo `(~(nom/tie x x) ~(nom/tie y y)) q))))
        '((a_0 a_1 a_1 (() ()))))))

(deftest cesk-identity-b
  (is (= (to-clj (run* (q) (nom/fresh [x] (evalo `(~(nom/tie x x) ~'(quote foo)) q))))
        '(foo))))

(deftest cesk-list-1
  (is (= (to-clj (run* (q) (evalo '(list (quote foo)) q)))
        '((foo)))))

(deftest cesk-list-2
  (is (= (to-clj (run* (q) (evalo '(list (quote foo) (quote bar)) q)))
        '((foo bar)))))

(deftest cesk-list-1-backwards
  (is (= (to-clj (run 3 (q) (evalo q '(foo))))
        '((quote (foo))
          (list (quote foo))
          ((fn [a_0] (quote (foo))) (quote _1))))))

(deftest cesk-list-2-backwards
  (is (=
        (to-clj
          (run 3 (q)
            (fresh [body]
              (nom/fresh [x]
                (evalo (nom/tie x body) '(foo))))))
        '())))

(deftest cesk-list-2b
  (is (= (to-clj
           (run 3 (q)
             (evalo q '(foo bar))))
        '((quote (foo bar))
          (list (quote foo) (quote bar))
          ((fn [a_0] (quote (foo bar))) (quote _1))))))

(deftest cesk-list-3
  (is (= (to-clj
           (run* (q)
             (nom/fresh [x]
               (evalo `(~'list ~'(quote baz)
                         (~(nom/tie x x) ~'(list (quote foo) (quote bar)))
                         (~(nom/tie x x) ~'(list (quote quux))))
                 q))))
        '((baz (foo bar) (quux))))))

(deftest cesk-shadowing-pseudo
  (is (= (to-clj
           (run* (q)
             (nom/fresh [x y quote]
               (evalo `(~(nom/tie x
                          `(~(nom/tie quote
                               `(~quote ~x))
                            ~(nom/tie y `(~'list ~y ~y ~y))))
                         ~'(quote bar))
                 q))))
        '((bar bar bar)))))

(defn quinec [x]
  `(~(nom/tie x
       `(~'list ~x (~'list ~'(quote quote) ~x)))
     (~'quote
       ~(nom/tie x
          `(~'list ~x (~'list ~'(quote quote) ~x))))))

(deftest cesk-quinec-forwards
  (is (= (to-clj
           (run* (q)
             (nom/fresh [x]
               (evalo (quinec x) q))))
        [(to-clj (quinec 'a_0))])))

(deftest cesk-quinec-both
  (is (= (to-clj
           (run 1 (q)
             (nom/fresh [x]
               (evalo (quinec x) (quinec x)))))
        '(_0))))

(deftest cesk-quote-bkwards-0
  (is (= (to-clj
           (run 1 (q)
             (evalo (quote (quote x)) (quote x))))
        '(_0))))

(deftest cesk-quote-bkwards-1
  (is (= (run 1 (q)
           (evalo '(quote (quote x)) '(quote x)))
        '(_0))))

(deftest cesk-quote-bkwards-2
  (is (= (to-clj
           (run 1 (q)
             (fresh (y)
               (== y 'x)
               (evalo `(~'quote ~y) q))))
        '(x))))

;;; generate k here
(deftest cesk-quinec-bkwards-a
  (is (= (to-clj
           (run 1 (q)
             (fresh [expr env store k val]
               (nom/fresh [closure-nom]
                 (eval-expo
                   closure-nom
                   expr
                   env
                   store
                   k
                   val)
                 (== [closure-nom expr env store k val] q)))))
        '(((a_0 (quote _1) _2 _3 (empty-k) _1) :- a_0#_1)))))

(deftest cesk-quinec-for-real
  (is (= (to-clj
           (run 1 (q)
             (evalo q q)))
        '(((fn [a_0] (list a_0 (list (quote quote) a_0))) (quote (fn [a_0] (list a_0 (list (quote quote) a_0)))))))))

(deftest twines
  (is (= (to-clj
           (run 1 (r)
             (fresh (p q)
               (!= p q)
               (evalo p q)
               (evalo q p)
               (== [p q] r))))
        '(((quote ((fn [a_0] (list (quote quote) (list a_0 (list (quote quote) a_0)))) (quote (fn [a_0] (list (quote quote) (list a_0 (list (quote quote) a_0)))))))
                  ((fn [a_0] (list (quote quote) (list a_0 (list (quote quote) a_0)))) (quote (fn [a_0] (list (quote quote) (list a_0 (list (quote quote) a_0)))))))) )))

(deftest cesk-quinec-for-real-3
  (is (= (to-clj
           (run 3 (q)
             (evalo q q)))
        '(((fn [a_0] (list a_0 (list 'quote a_0)))
            '(fn [a_0] (list a_0 (list 'quote a_0))))
          ((fn [a_0] (list a_0 (list 'quote ((fn [a_1] a_0) '_2))))
            '(fn [a_0] (list a_0 (list 'quote ((fn [a_1] a_0) '_2)))))
          ((fn [a_0] (list a_0 (list ((fn [a_1] 'quote) '_2) a_0)))
            '(fn [a_0] (list a_0 (list ((fn [a_1] 'quote) '_2) a_0))))))))

;; thrines don't come back
