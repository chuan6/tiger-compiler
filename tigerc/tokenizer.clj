(ns tokenizer
  (:require [clojure.string :as str]))

(def token-complex
  #{:id :comment :digits :string})

(def token-keyword
  #{:array :break :do :else :end :for :function :if :in
    :let :nil :of :then :to :type :var :while})

(def token-punct
  #{:comma :colon :semi-colon :open-paren :close-paren
    :open-bracket :close-bracket :open-brace :close-brace
    :period :plus :minus :star :slash :equal :diamond :lt
    :leq :gt :geq :and :pipe :assign})

(def token-set
  (clojure.set/union token-complex
                     token-keyword
                     token-punct))

(def token-queue clojure.lang.PersistentQueue/EMPTY)
;;print-method implementation is from Joy of Clojure(2nd edition)
(defmethod print-method clojure.lang.PersistentQueue [queue writer]
  (print-method '<- writer)
  (print-method (seq queue) writer)
  (print-method '-< writer))

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
    (search kwords (str (keyword s)))))

(defn id-recognizer [curr]
  (let [s (:char-seq curr)
        c (first s)]
    (assert (Character/isLetter c))
    (loop [s (rest s)
           t [c]]
      (let [c (first s)]
        (if (and c (or (Character/isLetterOrDigit c) (= c \_)))
          (recur (rest s) (conj t c))
          (let [token (str/join t)
                kword (keyword-recognizer token)]
            (if kword
              {:char-seq s :token-seq (conj (:token-seq curr)
                                            {:token kword})}
              {:char-seq s :token-seq (conj (:token-seq curr)
                                            {:token :id :name token})})))))))

(defn digits-recognizer [curr]
  (let [s (:char-seq curr)
        c (first s)]
    (assert (Character/isDigit c))
    (loop [s (rest s)
           t [c]]
      (let [c (first s)]
        (if (and c (Character/isDigit c))
          (recur (rest s) (conj t c))
          {:char-seq s :token-seq (conj (:token-seq curr)
                                        {:token :digits
                                         :value (str/join t)})})))))

(defn string-recognizer [curr]
  (let [s (:char-seq curr) q (:token-seq curr)
        c (first s)]
    (assert (= c \"))
    (let [suc (second s)]
      (case suc
        \"
        {:char-seq (rest (rest s))
         :token-seq (conj q {:token :string :value ""})}

        nil
        (do (println "String misses closing double-quote.")
            (assoc curr :char-seq ()))

        (loop [s (rest s)
               t [suc]
               consecutive-backslash-count 0]
          (assert (not (empty? s)))
          (if (empty? (rest s))
            (do (println "String" (str/join t)
                         "misses closing double quote.")
                (assoc curr :char-seq ()))
            (let [c   (first s)
                  suc (second s) ;suc is non-nil
                  cbc (if (= c \\) (inc consecutive-backslash-count)
                          0)]
              (if (and (= suc \") (even? cbc))
                {:char-seq (rest (rest s))
                 :token-seq (conj q {:token :string :value (str/join t)})}
                (recur (rest s) (conj t suc) cbc)))))))))

;;Note: as defined, comment supports nesting.
(defn comment-recognizer [curr ignore?]
  (let [s (:char-seq curr)]
    (assert (and (= (first s) \/) (= (second s) \*)))
    (loop [s (rest (rest s))
           t []
           flag-count 1] ;the number of comment opennings to be closed
      (if (or (empty? s) (empty? (rest s)))
        (do (println "Comment"
                     (str/join (if (empty? s) t (conj t (first s))))
                     "misses closing.")
            (assoc curr :char-seq ())) ;the problematic token is not recorded
        (let [c   (first s)
              suc (second s)]
          (cond (and (= c \*) (= suc \/)) ;closing
                (let [flag-count (dec flag-count)]
                  (if (= flag-count 0)
                    (let [curr (assoc curr :char-seq (rest (rest s)))]
                      (if ignore?
                        curr
                        (assoc curr :token-seq
                               (conj (:token-seq curr)
                                     {:token :comment :value (str/join t)}))))
                    (recur (rest (rest s)) ;note pattern */*
                           (-> t (conj c) (conj suc))
                           flag-count)))

                (and (= c \/) (= suc \*)) ;openning
                (let [flag-count (inc flag-count)]
                  (recur (rest (rest s)) ;note pattern /*/
                         (-> t (conj c) (conj suc))
                         flag-count))

                :else (recur (rest s) (conj t c) flag-count)))))))

(defn skip-spaces [curr]
  (let [s (:char-seq curr)
        c (first s)]
    (assert (Character/isWhitespace c))
    (loop [s (rest s)]
      (let [c (first s)]
        (if (and c (Character/isWhitespace c))
          (recur (rest s))
          (assoc curr :char-seq s))))))

(defn tokenize-str [s]
  (assert (string? s))
  (let [add-punct (fn [curr sym forward]
                    {:char-seq (nthrest (:char-seq curr) forward)
                     :token-seq (conj (:token-seq curr) {:token sym})})]
    (loop [curr {:char-seq s :token-seq token-queue}]
      (let [s (:char-seq curr)
            q (:token-seq curr)]
        (if (empty? s)
          (:token-seq curr)
          (let [c   (first s)
                suc (second s)] ;suc may be nil
            (cond
              (Character/isWhitespace c) ;skip leading spaces
              (recur (skip-spaces curr))
              
              (Character/isLetter c)     ;find an :id, or keyword token
              (recur (id-recognizer curr))

              (= c \")                   ;find a :string token
              (recur (string-recognizer curr))

              (Character/isDigit c)      ;find a :digits token
              (recur (digits-recognizer curr))

              (= c \/)                   ;find a :comment, or a :slash token
              (if (and suc (= suc \*))
                (recur (comment-recognizer curr true))
                (recur {:char-seq (rest s)
                        :token-seq (conj q {:token :slash})}))

              :else
              (case c
                \, (recur (add-punct curr :comma 1))
                \: (if (and suc (= suc \=))
                     (recur (add-punct curr :assign 2))
                     (recur (add-punct curr :colon 1)))
                \; (recur (add-punct curr :semi-colon 1))
                \( (recur (add-punct curr :open-paren 1))
                \) (recur (add-punct curr :close-paren 1))
                \[ (recur (add-punct curr :open-bracket 1))
                \] (recur (add-punct curr :close-bracket 1))
                \{ (recur (add-punct curr :open-brace 1))
                \} (recur (add-punct curr :close-brace 1))
                \. (recur (add-punct curr :period 1))
                \+ (recur (add-punct curr :plus 1))
                \- (recur (add-punct curr :minus 1))
                \* (recur (add-punct curr :star 1))
                \= (recur (add-punct curr :equal 1))
                \< (cond (and suc (= suc \>)) (recur (add-punct curr :diamond 2))
                         (and suc (= suc \=)) (recur (add-punct curr :leq 2))
                         :else (recur (add-punct curr :lt 1)))
                \> (if (and suc (= suc \=)) (recur (add-punct curr :geq 2))
                       (recur (add-punct curr :gt 1)))
                \& (recur (add-punct curr :and 1))
                \| (recur (add-punct curr :pipe 1))
                (:token-seq curr)))))))))

(defn norm-id-to-ty-id
  "find ALL cases where :id should be replaced by :ty-id, and replace them"
  [token-v]
  (assert (vector? token-v))
  (comment
    "Rules:"
    "- :id that immediately follows :colon is :ty-id;"
    "- :id that immediately follows :type is :ty-id;"
    "- :id that immediately follows :array :of is :ty-id;"
    "- :id that immediately follows :equal, which in turn,"
    "  immediately follows :type :ty-id is :ty-id;"
    "- :id that is immediately followed by { is :ty-id"
    "- :id that is immediately followed by [...] :of is :ty-id.")
  (let [v (transient token-v)
        n (count v)
        seq-1 [:colon]
        seq-2 [:type]
        seq-3 [:array :of]
        seq-4 [:type :ty-id :equal]

        follows?
        (fn [i sequence]
          ;;(println i sequence)
          (assert (= (:token (v i)) :id))
          (let [m (count sequence)]
            (if (< i m)
              false
              (loop [j (- i m) k 0]
                (if (= j i)
                  true
                  (if (= (:token (v j)) (sequence k))
                    (recur (inc j) (inc k))
                    false))))))

        followed-by-open-brace?
        (fn [i]
          (assert (= (:token (v i)) :id))
          (let [j (inc i)]
            (and (< j n) (= (:token (v j)) :open-brace))))

        followed-by-brackets-then-of?
        (fn [i]
          ;;(println i)
          (assert (= (:token (v i)) :id))
          (loop [flag 0 j (inc i)]
            (assert (>= flag 0))
            (if (= j n)
              false
              (let [t (:token (v j))]
                (if (= flag 0)
                  (if (= j (inc i))
                    (if (= t :open-bracket)
                      (recur (inc flag) (inc j)) false)
                    (if (= t :of)
                      true false))
                  (recur (case t
                           :open-bracket (inc flag)
                           :close-bracket (dec flag)
                           flag)
                         (inc j)))))))
        ]
    (loop [i 0 v v]
      (if (= i n)
        (persistent! v)
        (let [vi (v i)]
          (if (and (= (:token vi) :id)
                   (or (follows? i seq-1)
                       (follows? i seq-2)
                       (follows? i seq-3)
                       (follows? i seq-4)
                       (followed-by-open-brace? i)
                       (followed-by-brackets-then-of? i)))
            (recur (inc i) (assoc! v i {:token :ty-id :name (:name vi)}))
            (recur (inc i) v)))))))

(defn tokenize-file [path-to-file]
  (let [str (slurp path-to-file)
        tv (vec (tokenize-str str))]
    (norm-id-to-ty-id tv)))
