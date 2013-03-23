(ns cesk.utils
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom]))

(defn without-constraints [r]
  (if (= ':- (second r))
    (first r)
    r))

;;; prettier reification for single-variable constraints
(defn reifier-for [tag x]
  (fn [c v r a]
    (let [x (walk* r (walk* a x))]
      (when (symbol? x)
        `(~tag ~x)))))

;;; type constraints
(defn nomo [x] (predc x nom? (reifier-for 'nom x)))

(defn symbolo [x] (predc x symbol? (reifier-for 'sym x)))

(defn numbero [x] (predc x number? (reifier-for 'num x)))

;;; debugging
(defn debug-log [msg x]
  (fn [a] (println msg (-reify a x)) a))
