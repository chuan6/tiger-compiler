(ns cfg
  (:require [clojure.set :as set]))

(def empty-string 'ε)
(def end-marker '$)

(def sample
  {:terminal #{\+ \* \( \) 'id} ;TODO decide if add empty-string here
   :start 'expr
   :production
   {'expr        [['term 'expr-helper]] ;first as production for the start symbol
    'expr-helper [[\+ 'term 'expr-helper]   empty-string]
    'term        [['factor 'term-helper]]
    'term-helper [[\* 'factor 'term-helper] empty-string]
    'factor      [[\( 'expr \)] ['id]]}})

(defn terminal? [grammar x]
  (if (= x empty-string)
    true
    (contains? (:terminal grammar) x)))

(declare first-set-non-term)

(defn first-set-production [g p s]
  (if (= p empty-string)
    #{empty-string}
    (if (empty? p)
      s
      (let [x (first p)]
        (if (terminal? g x)
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

;(def init-follow-set
 ; {'expr #{} 'expr-helper #{}
  ; 'term #{} 'term-helper #{}
   ;'factor #{}})

(defn init-follow-set [grammar]
  (let [p (seq (:production grammar))]
    (loop [result {}
           ps     p]
      (if (empty? ps)
        result
        (let [nt (nth (first ps) 0)]
          (recur (assoc result nt
                        (if (= nt (:start grammar))
                          #{end-marker} #{}))
                 (rest ps)))))))

(defn init-data [grammar]
  {:set (init-follow-set grammar)
   :infer (fn [x] x)})

(defn non-terminal? [grammar x]
  (let [ps (:production grammar)]
    (not (nil? (get ps x)))))

(defn add-to-follow-set [data nt new]
  (assoc data nt (set/union (get data nt)
                            (disj new empty-string))))

(defn iterate-til-fixed [f x]
  (let [x' (f x)]
    (if (= x' x) x (iterate-til-fixed f x')))) ;powerful '=' operation!

(defn ff [f x y]
  (fn [s] (let [s (f s)]
               (assoc s y (set/union (get s x) (get s y))))))

(defn follow-set-production [grammar left right data]
  (loop [right right
         data data]
    (if (empty? right)
      data
      (let [x (first right)
            xs (rest right)]
        (cond
          (terminal? grammar x) (recur xs data)
          (non-terminal? grammar x)
          (let [x-next (first-set grammar xs)
                curr-set (add-to-follow-set (:set data) x x-next)]
              (if (or (empty? x-next) (contains? x-next empty-string))
                (recur xs
                       {:set curr-set :infer (ff (:infer data) left x)})
                (recur xs
                       {:set curr-set :infer (:infer data)}))))))))

(defn follow-set [grammar]
  (let [prods (seq (:production grammar))]
    (loop [prods prods
           data (init-data grammar)]
      (if (empty? prods)
        (iterate-til-fixed (:infer data) (:set data))
        (recur (rest prods)
               (let [prod (first prods)
                     left (nth prod 0)]
                 (loop [alts (nth prod 1)
                        data data]
                   (if (empty? alts)
                     data
                     (let [right (first alts)]
                       (if (= right empty-string)
                         (recur (rest alts) data)
                         (recur (rest alts)
                                (follow-set-production grammar left right data))))))))))))


