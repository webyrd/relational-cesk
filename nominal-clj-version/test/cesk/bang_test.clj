(ns cesk.bang_test
  (:use [cesk.lookupo] :reload)
  (:use [cesk.bang] :reload)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom])
  (:use [clojure.test]))

(defn tagged-list? [tag x]
  (and (coll? x) (= tag (first x))))

(defn to-clj [x]
  (cond
    (tagged-list? 'fn x)
    `(~'fn [~(:binding-nom (second x))] ~(to-clj (:body (second x))))
    (tagged-list? 'letcc x)
    `(~'letcc ~(:binding-nom (second x)) ~(to-clj (:body (second x))))
    (and (coll? x) (not (empty? x)))
    (cons (to-clj (first x)) (to-clj (rest x)))
    :else x))

(deftest cesk-quote-a
  (is (= (to-clj (run* (q) (evalo '(quote x) q)))
        '(x))))

(deftest cesk-quote
  (is (= (to-clj (run* (q) (nom/fresh [x] (evalo `(quote (~'fn ~(nom/tie x x))) q))))
        '((fn [a_0] a_0)))))

(deftest cesk-list-0
  (is (= (to-clj (run* (q) (evalo '(list) q)))
        '(()))))

(deftest cesk-closure
  (is (= (to-clj (run* (q) (nom/fresh [x] (evalo `(~'fn ~(nom/tie x x)) q))))
        '((a_0 a_1 a_1 (() ()))))))

(deftest cesk-identity-a
  (is (= (to-clj (run* (q) (nom/fresh [x y] (evalo `((~'fn ~(nom/tie x x)) (~'fn ~(nom/tie y y))) q))))
        '((a_0 a_1 a_1 (() ()))))))

(deftest cesk-identity-b
  (is (= (to-clj (run* (q) (nom/fresh [x] (evalo `((~'fn ~(nom/tie x x)) ~'(quote foo)) q))))
        '(foo))))

(deftest cesk-list-1
  (is (= (to-clj (run* (q) (evalo '(list (quote foo)) q)))
        '((foo)))))

(deftest cesk-list-2
  (is (= (to-clj (run* (q) (evalo '(list (quote foo) (quote bar)) q)))
        '((foo bar)))))

(deftest cesk-set!-1
  (is (=
        (to-clj
          (run* (q)
            (nom/fresh [x ignore]
              (evalo `((~'fn ~(nom/tie x
                                `((~'fn ~(nom/tie ignore x))
                                  (~'set ~x ~'(quote 5)))))
                        ~'(quote 6))
                q))))
        '(5))))

(deftest cesk-set!-backwards-1
  (is (=
        (to-clj
          (run 2 (q)
            (nom/fresh [x ignore]
              (evalo `((~'fn ~(nom/tie x
                                `((~'fn ~(nom/tie ignore x))
                                   ~q)))
                        ~'(quote 6))
                '5))))
        '((throw (quote (empty-k)) (quote 5))
           (set a_0 (quote 5))))))

(deftest letcc-throw-0
  (is (=
        (to-clj
          (run* (q)
            (nom/fresh [k]
              (evalo `(~'letcc ~(nom/tie k k)) q))))
        '((empty-k)))))

(deftest letcc-throw-0b
  (is (= (to-clj
           (run* (q)
             (nom/fresh [k]
               (evalo `(~'letcc ~(nom/tie k '(quote 1))) q))))
        '(1))))

(deftest letcc-throw-0c
  (is (= (to-clj
           (run* (q)
             (nom/fresh [k]
               (evalo `(~'letcc ~(nom/tie k `(~'throw ~k ~'(quote 1)))) q))))
        '(1))))

(deftest letcc-throw-2a
  (is (= (to-clj
           (run* (q)
             (nom/fresh [k x y]
               (evalo `(~'letcc ~(nom/tie k
                                   `((~'fn ~(nom/tie x x))
                                      (~'throw ~k (~'fn ~(nom/tie y y))))))
                 q))))
        '((a_0 a_1 a_1 ((a_2) (a_3)))))))

(deftest letcc-throw-2b
  (is (= (to-clj
           (run* (q)
             (nom/fresh [k x]
               (evalo `(~'letcc ~(nom/tie k
                                   `((~'fn ~(nom/tie x '(quote 5)))
                                      (~'throw ~k ~'(quote 7)))))
                 q))))
        '(7))))

(deftest letcc-throw-2c
  (is (= (to-clj
           (run* (q)
             (nom/fresh [k]
               (evalo `(~'letcc ~(nom/tie k
                                   `(~'(quote 5)
                                      (~'throw ~k ~'(quote 7)))))
                 q))))
        '(7))))

(deftest cesk-list-1-backwards
  (is (= (to-clj
           (run 3 (q)
             (evalo q '(foo))))
        '((quote (foo))
          (letcc a_0 (quote (foo)))
          (letcc a_0 (letcc a_1 (quote (foo))))))))

(deftest cesk-list-2-backwards
  (is (= (to-clj
           (run 3 (q)
             (fresh [body]
               (nom/fresh [x]
                 (evalo `(~'fn ~(nom/tie x body)) '(foo))))))
        '())))

(deftest cesk-list-2b
  (is (= (to-clj
           (run 3 (q)
             (evalo q '(foo bar))))
        '((quote (foo bar))
          (letcc a_0 (quote (foo bar)))
          (letcc a_0 (letcc a_1 (quote (foo bar))))))))

(deftest cesk-list-3
  (is (= (to-clj
           (run* (q)
             (nom/fresh [x]
               (evalo `(~'list ~'(quote baz)
                         ((~'fn ~(nom/tie x x)) ~'(list (quote foo) (quote bar)))
                         ((~'fn ~(nom/tie x x)) ~'(list (quote quux))))
                 q))))
        '((baz (foo bar) (quux))))))

(deftest cesk-shadowing-pseudo
  (is (= (to-clj
           (run* (q)
             (nom/fresh [x y quote]
               (evalo `((~'fn ~(nom/tie x
                                 `((~'fn ~(nom/tie quote
                                            `(~quote ~x)))
                                    (~'fn ~(nom/tie y `(~'list ~y ~y ~y))))))
                         ~'(quote bar))
                 q))))
        '((bar bar bar)))))

(defn quinec [x]
  `((~'fn ~(nom/tie x
             `(~'list ~x (~'list ~'(quote quote) ~x))))
     (~'quote
       (~'fn ~(nom/tie x
                `(~'list ~x (~'list ~'(quote quote) ~x)))))))

(deftest cesk-quinec-forwards
  (is (= (to-clj
           (run* (q)
             (nom/fresh [x]
               (evalo (quinec x) q))))
        [(to-clj (quinec 'a_0))])))

(deftest cesk-quinec-both
  (is (= (run 1 (q)
           (nom/fresh [x]
             (evalo (quinec x) (quinec x))))
        '(_0))))

(deftest cesk-quote-bkwards-0
  (is (= (run 1 (q)
           (evalo (quote (quote x)) (quote x)))
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

(deftest cesk-quinec-bkwards-a
  (is (= (to-clj
           (run 1 (q)
             (nom/fresh [x]
               (== (quinec x) q)
               (evalo q (quinec x)))))
        [(to-clj (quinec 'a_0))])))

(deftest cesk-fresh-bkwards
  (is (= (to-clj
            (run 3 (q)
              (fresh (expr v)
                (evalo expr v)
                (== [expr v] q))))
        '(((quote _0) _0)
          ((fn [a_0] _1) (a_2 a_0 _1 (() ())))
          ((letcc a_0 (quote _1)) _1)))))
