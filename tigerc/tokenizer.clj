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

(defn get-keyword
  "get corresponding keyword, otherwise nil, for a token"
  {:test
   #(let [kwords     (map name token-keyword)
          non-kwords (map (partial str "1") kwords)]
      (assert (empty? (clojure.set/intersection (set kwords)
                                                (set non-kwords)))
              "ineffective test!")
      (doall
       (concat
        (for [kw kwords]
          (assert (contains? token-keyword (get-keyword kw))))
        (for [nkw non-kwords]
          (assert (nil? (get-keyword nkw)))))))}

  [s]
  (token-keyword (keyword s)))

(defn id-recognizer
  {:test
   #(let [ids    ["x" "x1" "x_1" "x_1_"]
          kwords (map name token-keyword)]
      (assert (empty? (clojure.set/intersection (set ids)
                                                (set kwords)))
              "ineffective test!")
      (doall
       (concat
        (for [id ids]
          (assert (= [() {:token :id :name id}]
                     (id-recognizer (seq id)))))
        (for [kw kwords]
          (assert (= [() {:token (keyword kw)}]
                     (id-recognizer (seq kw))))))))}
  [source]
  (let [c (first source)]
    (assert (Character/isLetter c))
    (loop [s (rest source)
           t [c]]
      (let [c (first s)]
        (if (and c (or (Character/isLetterOrDigit c) (= c \_)))
          (recur (rest s) (conj t c))
          (let [token (str/join t)
                kword (get-keyword token)]
            (if kword
              [s {:token kword}]
              [s {:token :id :name token}])))))))

(defn digits-recognizer
  {:test
   #(let [all-digits ["0" "1" "123" "123"]
          tail "f"
          with-non-digit-tail (map (fn [ds] (str ds tail)) all-digits)]
      (doall
       (concat
        (for [ds all-digits]
          (assert (= [() {:token :digits :value ds}]
                     (digits-recognizer (seq ds)))))
        (for [ts with-non-digit-tail]
          (let [[s t] (digits-recognizer (seq ts))]
            (assert (= s (seq tail)))
            (assert (= (str (:value t) tail) ts)))))))}
  [source]
  (let [c (first source)]
    (assert (Character/isDigit c))
    (loop [s (rest source)
           t [c]]
      (let [c (first s)]
        (if (and c (Character/isDigit c))
          (recur (rest s) (conj t c))
          [s {:token :digits :value (str/join t)}])))))

(defn string-recognizer
  {:test ;TODO add test case: string with escaped quotes
   #(let [strings ["\"\"" "\"hello, world\""]
          missing-closing-quote (map (fn [s]
                                       (subs s 0 (dec (count s))))
                                     strings)
          tail " "
          with-tail (map (fn [s] (str s tail)) strings)]
      (doall
       (concat
        (for [s strings]
          (assert (= [() {:token :string :value (read-string s)}]
                     (string-recognizer (seq s)))))
        (for [m missing-closing-quote]
          (assert (= [(seq m)]
                     (string-recognizer (seq m)))))
        (for [ts with-tail]
          (let [[s t] (string-recognizer (seq ts))]
            (assert (= s (seq tail)))
            (assert (= (str \" (:value t) \" tail) ts)))))))}
  [source]
  (let [c (first source)]
    (assert (= c \"))
    (let [suc (second source)]
      (case suc
        \"
        [(rest (rest source)) {:token :string :value ""}]

        nil
        (do (println "String misses closing double-quote.")
            [source])

        (loop [s (rest source)
               t [suc]
               consecutive-backslash-count 0]
          (assert (not (empty? s)))
          (if (empty? (rest s))
            (do (println "String" (str/join t)
                         "misses closing double quote.")
                [source])
            (let [c   (first s)
                  suc (second s) ;suc is non-nil
                  cbc (if (= c \\) (inc consecutive-backslash-count)
                          0)]
              (if (and (= suc \") (even? cbc))
                [(rest (rest s)) {:token :string :value (str/join t)}]
                (recur (rest s) (conj t suc) cbc)))))))))

(def comment-opening [\/ \*])
(def comment-closing [\* \/])
(defn comment-recognizer
  {:test
   #(let [carve-out (fn [cmt] (subs cmt 2 (- (count cmt) 2)))
          cmts ["/**/"
                "/*hello*/"
                "/*hello\nworld*/"
                "/*comment looks like this: /*...*/*/"]
          ambiguous ["/*/" "/*/*/"]
          missing-closing (->> cmts
                               (map (comp (partial str "/*") carve-out))
                               (concat ambiguous))
          tail "*/"
          with-tail (map (fn [s] (str s tail)) cmts)]
      (doall
       (concat
        (for [cmt cmts]
          (assert (= [() {:token :comment :value (carve-out cmt)}]
                     (comment-recognizer (seq cmt)))))
        (for [m missing-closing]
          (assert (= [(seq m)]
                     (comment-recognizer (seq m)))))
        (for [ts with-tail]
          (let [[s t] (comment-recognizer (seq ts))]
            (assert (= s (seq tail)))
            (assert (= (str "/*" (:value t) "*/" tail) ts)))))))}
  [source]
  (let [[s0 s1 & smore] source]
    (assert (= [s0 s1] comment-opening))
    (let [pairs (as-> smore $
                     (concat $ [\space]) ;left-shifted
                     (partition 2 1 $))]
      (letfn [(recursive-cmt-reader [pairs]
                (loop [[p & pmore :as ps] pairs
                       cv []]
                  (cond
                    (empty? ps)
                    [ps cv false]

                    (= p comment-closing)
                    [(rest pmore) cv true]

                    (= p comment-opening)
                    (let [[ps' cv'] (recursive-cmt-reader (rest pmore))]
                      (recur ps' (into cv (concat comment-opening
                                                  cv'
                                                  comment-closing))))

                    :else
                    (recur pmore (conj cv (first p))))))]
        (let [[remaining-pairs
               collected-cmt
               with-closing?] (recursive-cmt-reader pairs)]
          (if with-closing?
            [(map first remaining-pairs)
             {:token :comment :value (str/join collected-cmt)}]
            (do (println "missing comment closing")
                [source])))))))

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
