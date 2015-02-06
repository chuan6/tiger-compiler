(ns cfg
  (:require [clojure.set :as set]))

(def empty-string 'ε)
(def end-mark '$)

(def sample
  {:terminal #{\+ \* \( \) 'id} ;TODO decide if add empty-string here
   :production
   {'expr        [['term 'expr-helper]]
    'expr-helper [[\+ 'term 'expr-helper]   empty-string]
    'term        [['factor 'term-helper]]
    'term-helper [[\* 'factor 'term-helper] empty-string]
    'factor      [[\( 'expr \)] ['id]]
    } ;number is index in :terminal
   })

(declare first-set-non-term)

(defn first-set-production [g p s]
  (if (= p empty-string)
    #{empty-string}
    (if (empty? p)
      s
      (let [x (first p)]
        (if (contains? (:terminal g) x)
          (conj s x)
          (let [r (first-set-non-term g x)
                ss (set/union s r)]
            (if (contains? r empty-string)
              (first-set-production g (rest p) ss)
              ss)))))))

(defn first-set-non-term [grammar nt]
  (let [right (get (:production grammar) nt)
        n-alts (count right)]
    (loop [i   0
           tmp #{}]
      (if (= i n-alts)
        tmp
        (recur (inc i)
               (set/union tmp (first-set-production grammar (nth right i) #{})))))))

(defn first-set [grammar string]
  (first-set-production grammar string #{}))

(defn follow-set [])



