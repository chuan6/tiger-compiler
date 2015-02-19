(ns tiger
  (:require [clojure.string :as str]))

(def token-complex
  #{'id 'comment 'digits 'string})

(def token-keyword
  #{'array 'break 'do 'else 'end 'for 'function 'if 'in
    'let (symbol "nil") 'of 'then 'to 'type 'var 'while})

(def token-punct
  #{'comma 'colon 'semi-colon 'open-paren 'close-paren
    'open-bracket 'close-bracket 'open-brace 'close-brace
    'period 'plus 'minus 'star 'slash 'equal 'angle 'lt
    'leq 'gt 'geq 'and 'pipe 'assign})

(def token-set
  (clojure.set/union token-complex
                     token-keyword
                     token-punct))

(def token-queue clojure.lang.PersistentQueue/EMPTY)

(defn tree-insert [tree key comp-fn]
  (if tree
    (let [c (comp-fn key (:key tree))]
      (cond (< c 0) (assoc tree :left
                           (tree-insert (:left tree) key comp-fn))
            (> c 0) (assoc tree :right
                           (tree-insert (:right tree) key comp-fn))
            :else tree))
    {:key key :left nil :right nil}))

(defn tree-search [tree key comp-fn]
  (if tree
    (let [c (comp-fn key (:key tree))]
      (cond (< c 0) (tree-search (:left tree) key comp-fn)
            (> c 0) (tree-search (:right tree) key comp-fn)
            :else (:key tree)))))

(defn keyword-recognizer [s]
  (let [insert (fn [tree key]
                 (tree-insert tree key (fn [x y] (compare (str x) (str y)))))
        search (fn [tree key]
                 (tree-search tree key (fn [x y] (compare x (str y)))))
        kwords (reduce insert nil token-keyword)]
    (search kwords s)))

(defn id-recognizer [curr]
  (assert (Character/isLetter (first (:rest curr))))
  (loop [t [(first (:rest curr))]
         s (rest (:rest curr))]
    (let [c (first s)]
      (if (Character/isLetterOrDigit c)
        (recur (conj t c) (rest s))
        {:char-seq s
         :token-seq (conj (:token-seq curr)
                          {:token 'id :name (str/join t)})}))))

(defn string-recognizer [curr]
  (assert (= (first (:char-seq curr)) \"))
  (let [s (rest (:char-seq curr))
        token-seq (:token-seq curr)]
    (if (= (first s) \") ;if true, empty string found
      {:char-seq (rest s)
       :token-seq (conj token-seq {:token 'string :value ""})}
      (loop [s s
             t []
             consecutive-backslash-count 0]
        (if (or (empty? s) (empty? (rest s)))
          (do (println "String" (str/join t) "misses closing double-quote.")
              (assoc curr :char-seq nil)) ;the problematic token is not recorded
          (let [c    (first s)
                peek (second s) ;c and peek are non-nil
                cbc  (if (= c \\) (inc consecutive-backslash-count)
                         0)]
            (if (and (= peek \") (even? consecutive-backslash-count))
              {:char-seq (rest (rest s))
               :token-seq (conj token-seq
                                {:token 'string :value (str/join (conj t c))})}
              (recur (rest s) (conj t c) cbc))))))))

;;Note: as defined, comment supports nesting.
(defn comment-recognizer [curr]
  (let [s (:char-seq curr)]
    (assert (and (= (first s) \/) (= (second s) \*)))
    (let [nest-handler (fn [f s]
                         (loop [s (rest (rest s))
                                t [\/ \*]]
                           (if (or (empty? s) (empty? (rest s)))
                             (do (println "Incomplete comment nesting.")
                                 (if (empty? s)
                                   [t s]
                                   [(conj t (first s)) (rest s)]))
                             (let [c   (first s)
                                   suc (second s)]
                               (cond
                                 (and (= c \/) (= suc \*)) ;nesting comment
                                 (let [[t1 s] (f s)]
                                   (recur s (concat t t1)))

                                 (and (= c \*) (= suc \/)) ;end
                                 [(-> t (conj \*) (conj \/))
                                  (rest (rest s))]

                                 :else (recur (rest s) (conj t c)))))))]
      (loop [s (rest (rest s))
             t []]
        (if (or (empty? s) (empty? (rest s)))
          (do (println "Comment" (str/join t) "misses closing */.")
              (assoc curr :char-seq nil))
          (let [c   (first s)
                suc (second s)] ;c ans suc are non-nil
            (cond
              (and (= c \/) (= suc \*)) ;nesting comment
              (let [[t1 s] (nest-handler nest-handler s)]
                (recur s (vec (concat t t1)))) ;note: concat return lazy seq instead of vector

              (and (= c \*) (= suc \/)) ;end
              {:char-seq (rest (rest s))
               :token-seq (conj (:token-seq curr) {:token 'comment :value (str/join t)})}

              :else (recur (rest s) (conj t c)))))))))

(defn tokenize [in]
  )
