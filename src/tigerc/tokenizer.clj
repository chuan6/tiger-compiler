(ns tigerc.tokenizer
  (:require [clojure.data :refer [diff]]
            [clojure.string :as str]
            [clojure.test :as t]
            [tigerc.test :as tt]))

(def token-complex
  #{:id :ty-id :comment :digits :string})

(def token-keyword
  #{:array :break :do :else :end :for :function :if :in
    :let :nil :of :then :to :type :var :while})

(def token-punct
  {[\: \=] :assign
   [\< \=] :leq
   [\[]    :open-bracket
   [\.]    :period
   [\*]    :star
   [\)]    :close-paren
   [\+]    :plus
   [\(]    :open-paren
   [\:]    :colon
   [\,]    :comma
   [\;]    :semi-colon
   [\&]    :and
   [\>]    :gt
   [\<]    :lt
   [\}]    :close-brace
   [\> \=] :geq
   [\]]    :close-bracket
   [\{]    :open-brace
   [\-]    :minus
   [\=]    :equal
   [\/]    :slash
   [\< \>] :diamond,
   [\|]    :pipe})

(def token-set
  (clojure.set/union token-complex
                     token-keyword
                     (set (vals token-punct))))

(def empty-queue clojure.lang.PersistentQueue/EMPTY)
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
      (tt/comprehend-tests
       (for [kw kwords]
         (contains? token-keyword (get-keyword kw)))
       (for [nkw non-kwords]
         (nil? (get-keyword nkw)))))}
  [s]
  (token-keyword (keyword s)))

(defn- without-prefix [origin prefix]
  (loop [s origin t prefix]
    (cond
      (empty? t) s
      (not= (first s) (first t)) origin
      :else (recur (rest s) (rest t)))))

(defn id-recognizer
  {:test
   #(let [ids    ["x" "x1" "x_1" "x_1_"]
          kwords (map name token-keyword)]
      (tt/comprehend-tests
       (for [id ids
             :let [[s t] (id-recognizer (seq id))]]
         [(t/is (= (vec id) s))
          (t/is (= {:token :id :name id} t))])
       (for [kw kwords
             :let [[s t] (id-recognizer (seq kw))]]
         [(t/is (= (vec kw) s))
          (t/is (= {:token (keyword kw)} t))])))}
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
              [t {:token kword}]
              [t {:token :id :name token}])))))))

(defn digits-recognizer
  {:test
   #(let [all-digits ["0" "1" "123"]
          tail "f"
          with-non-digit-tail (map (fn [ds] (str ds tail)) all-digits)]
      (tt/comprehend-tests
       (for [ds all-digits
             :let [[s t] (digits-recognizer (seq ds))]]
         [(t/is (= (vec ds) s))
          (t/is (= {:token :digits :value ds} t))])
       (for [ts with-non-digit-tail
             :let [[s t] (digits-recognizer (seq ts))]]
         [(t/is (= (vec tail) (without-prefix ts s)))
          (t/is (= ts (str (:value t) tail)))])))}
  [source]
  (let [c (first source)]
    (assert (Character/isDigit c))
    (loop [s (rest source)
           t [c]]
      (let [c (first s)]
        (if (and c (Character/isDigit c))
          (recur (rest s) (conj t c))
          [t {:token :digits :value (str/join t)}])))))

(defn string-recognizer
  {:test
   #(let [strings ["\"\"" "\"say\"" "\"say \\\"hello, world!\\\"\""]
          missing-closing-quote (map (fn [s]
                                       (subs s 0 (dec (count s))))
                                     strings)
          tail " "
          with-tail (map (fn [s] (str s tail)) strings)]
      (tt/comprehend-tests
       (for [cs strings
             :let [[s t] (string-recognizer (seq cs))]]
         [(t/is (= (vec cs) s))
          (t/is (= {:token :string :value (subs cs 1 (dec (count cs)))} t))])
       (for [m missing-closing-quote]
         (t/is (= [[]] (string-recognizer (seq m)))))
       (for [ts with-tail
             :let [[s t] (string-recognizer (seq ts))]]
         [(t/is (= (vec tail) (without-prefix ts s)))
          (t/is (= ts (str \" (:value t) \" tail)))])))}
  [source]
  (let [c (first source)]
    (assert (= c \"))
    (loop [[s :as ss] (rest source)
           ts [c]
           consecutive-backslash-count 0]
      (cond
        (empty? ss)
        (do (println "String misses closing double-quote")
            [[]])

        (and (= s \") (even? consecutive-backslash-count))
        (let [processed (conj ts \")
              recognized (subvec ts 1)]
          [processed {:token :string :value (str/join recognized)}])

        (= s \\)
        (recur (rest ss) (conj ts \\) (inc consecutive-backslash-count))

        :else
        (recur (rest ss) (conj ts s) 0)))))

(def comment-opening [\/ \*])
(def comment-closing [\* \/])
(defn comment-recognizer
  {:test
   #(let [cons-cmt (fn [with-closing? s]
                     (cond-> comment-opening
                       true          (into (vec s))
                       with-closing? (into comment-closing)
                       true          str/join))
          texts [""
                 "hello"
                 "hello\nworld"
                 "comment looks like this: /*...*/"]
          cmts (map (partial cons-cmt true) texts)
          ambiguous ["/*/" "/*/*/"]
          missing-closing (-> (map (partial cons-cmt false) texts)
                              (into ambiguous))
          tail "*/"
          with-tail (map (fn [s] (str s tail)) cmts)]
      (tt/comprehend-tests
       (for [cmt cmts
             :let [[s t] (comment-recognizer (seq cmt))]]
         [(t/is (= (vec cmt) s))
          (t/is (= {:token :comment :value cmt} t))])
       (for [m missing-closing]
         (t/is (= [[]] (comment-recognizer (seq m)))))
       (for [ts with-tail
             :let [[s t] (comment-recognizer (seq ts))]]
         [(t/is (= (vec tail) (without-prefix ts s)))
          (t/is (= ts (str (:value t) tail)))])))}
  [source]
  (let [[s0 s1 :as ss] source]
    (assert (= [s0 s1] comment-opening))
    (let [pairs (as-> ss $
                  (concat $ [\space]) ;left-shifted
                  (partition 2 1 $))]
      (letfn [(cmt-reader [[p & pmore]]
                (assert (= p comment-opening))
                (loop [[p & pmore :as ps] (rest pmore)
                       cv comment-opening]
                  (cond
                    (empty? ps)
                    [() cv false]

                    (= p comment-closing)
                    [(rest pmore) (into cv comment-closing) true]

                    (= p comment-opening)
                    (let [[ps' cv' with-closing?] (cmt-reader ps)]
                      (if with-closing?
                        (recur ps' (into cv cv'))
                        [() (into cv cv') false]))

                    :else
                    (recur pmore (conj cv (first p))))))]
        (let [[_ cmt with-closing?] (cmt-reader pairs)]
          (if with-closing?
            [cmt {:token :comment :value (str/join cmt)}]
            (do (println "missing comment closing")
                [[]])))))))

(defn punct-recognizer
  {:test
   #(let [puncts (map str/join (keys token-punct))
          tail " "
          with-tail (map (fn [x] (str x tail)) puncts)]
      (tt/comprehend-tests
       (for [p puncts
             :let [[s t] (punct-recognizer (seq p))]]
         [(t/is (= (vec p) s))
          (t/is (= {:token (token-punct (vec p))} t))])
       (for [w with-tail
             :let [[s t] (punct-recognizer (seq w))]]
         [(t/is (= (vec tail) (without-prefix w s)))
          (t/is (= (token-punct s) (:token t)))])))}
  [[c c' :as source]]
  (let [t (token-punct [c])]
    (assert t)
    (if-let [t' (token-punct [c c'])]
      [[c c'] {:token t'}]
      [[c] {:token t}])))

(defn tokenize-str
  {:test
   #(let [string-value "hello"
          src {:spaces  " "
               :id      "x"
               :string  (str \" string-value \")
               :digits  "0"
               :comment "/*...*/"
               :plus    "+"
               :illegal "%"}
          variations (for [x (keys src)
                           y (keys src)
                           :let [pair [x y]]
                           :when (nil? (#{[:spaces :spaces]
                                          [:id :id]
                                          [:id :digits]
                                          [:digits :digits]} pair))]
                       pair)
          mock (fn [k] (cond-> {:token k}
                         (= k :id)      (assoc :name  (:id src))
                         (= k :string)  (assoc :value string-value)
                         (= k :digits)  (assoc :value (:digits src))
                         (= k :comment) (assoc :value (:comment src))))]
      (tt/comprehend-tests
       (for [pair variations
             :let [r (tokenize-str (str/join ((apply juxt pair) src)))]]
         (if (= (first pair) :illegal)
           (t/is (= empty-queue r))
           (t/is (= (map mock (remove #{:spaces :illegal} pair)) r))))))}
  [s]
  (assert (string? s))
  (let [skip-spaces (partial drop-while #(Character/isWhitespace %))
        inject (fn [env [processed recognized]]
                 (cond-> (update env :char-seq
                                 (comp skip-spaces without-prefix)
                                 processed)
                   recognized (update :token-seq conj recognized)))
        puncts (set (seq ",:;()[]{}.+-*/=<>&|"))]
    (loop [{:keys [char-seq] :as curr-env}
           {:char-seq (skip-spaces s) :token-seq empty-queue}]
      (let [recognizer (let [[c c'] char-seq]
                         (cond
                           ;;consume an :id, or keyword token
                           (and c (Character/isLetter c)) id-recognizer

                           ;;consume a :string token
                           (= c \") string-recognizer

                           ;;consume a :digits token
                           (and c (Character/isDigit c)) digits-recognizer

                           ;;consume a :comment
                           (= [c c'] comment-opening) comment-recognizer

                           ;;consume the rest of defined symbols
                           (puncts c) punct-recognizer

                           :else (partial conj [])))
            [processed :as ret] (recognizer char-seq)]
        (if (empty? processed) ;check if fixpoint is reached
          (:token-seq curr-env)
          (recur (inject curr-env ret)))))))

(defn norm-id-to-ty-id
  "find ALL cases where :id should be replaced by :ty-id, and replace them"
  {:test
   #(let [target
          {:token :id :name "int"}

          essential-forms
          [[{:token :colon} :slot]
           [{:token :type } :slot]
           [{:token :type } :slot {:token :equal} :slot]
           [{:token :array} {:token :of} :slot]
           [:slot {:token :open-brace}]
           [:slot {:token :open-bracket}
            {:token :digits :value "2"}
            {:token :close-bracket} {:token :of}]]

          broken-forms
          (mapv (fn [[v0 & v]]
                  (into [v0 {:token :if}] v))
                essential-forms)

          slot-to-id
          (partial replace {:slot target})

          slot-to-ty-id
          (partial replace {:slot (assoc target :token :ty-id)})]
      (tt/comprehend-tests
       (for [v essential-forms]
         (t/is (= (slot-to-ty-id v) (norm-id-to-ty-id (slot-to-id v)))))
       (for [v broken-forms]
         (t/is (= (slot-to-id v) (norm-id-to-ty-id (slot-to-id v)))))))}
  [tokens]
  (comment
    "Rules:"
    "- :id that immediately follows :colon is :ty-id;"
    "- :id that immediately follows :type is :ty-id;"
    "- :id that immediately follows :array :of is :ty-id;"
    "- :id that immediately follows :equal, which in turn,"
    "  immediately follows :type :ty-id is :ty-id;"
    "- :id that is immediately followed by { is :ty-id"
    "- :id that is immediately followed by [...] :of is :ty-id.")
  (let [tokens-without-cmts (remove #(= (:token %) :comment) tokens)

        pattern-1 [:colon]
        pattern-2 [:type]
        pattern-3 [:array :of]
        pattern-4 [:type :ty-id :equal]

        follows?
        (fn [[prevs _] pattern]
          (loop [xs prevs ys pattern]
            (if (empty? ys)
              true
              (let [x (peek xs) y (peek ys)]
                (if (not= (:token x) y)
                  false
                  (recur (pop xs) (pop ys)))))))

        followed-by-open-brace?
        (fn [[_ [x y]]]
          (= (:token y) :open-brace))

        skip-matching-brackets
        (fn [s]
          (assert (= (:token (first s)) :open-bracket))
          (loop [cnt 1
                 [x :as xs] (rest s)]
            (if (or (= cnt 0) (empty? xs))
              xs
              (recur ((condp = (:token x)
                        :open-bracket inc
                        :close-bracket dec
                        identity) cnt)
                     (rest xs)))))

        followed-by-matching-brackets-then-of?
        (fn [[_ [x & xs]]]
          (and (= (:token (first xs)) :open-bracket)
               (= (:token (first (skip-matching-brackets xs))) :of)))
        ]
    (loop [[ret-stack [t & ts] :as curr] [[] tokens-without-cmts]]
      (if (nil? t)
        ret-stack
        (recur
         [(conj ret-stack
                (cond-> t
                  (and (= (:token t) :id)
                       (or (follows? curr pattern-1)
                           (follows? curr pattern-2)
                           (follows? curr pattern-3)
                           (follows? curr pattern-4)
                           (followed-by-open-brace? curr)
                           (followed-by-matching-brackets-then-of? curr)))
                  (assoc :token :ty-id)))
          ts])))))

(defn tokenize-file [path-to-file]
  (let [tokens-by-first-pass (-> path-to-file
                                 slurp
                                 tokenize-str)
        tokens-by-second-pass (norm-id-to-ty-id tokens-by-first-pass)
        within-token-set? (fn [ts]
                            (empty? (remove token-set (map :token ts))))]
    (t/is (within-token-set? tokens-by-first-pass))
    (t/is (within-token-set? tokens-by-second-pass))
    ;;only comment removal and id-to-ty-id normalization happen in second pass
    (tt/comprehend-tests
     (for [[x y] (map vector
                      (remove #(= (:token %) :comment) tokens-by-first-pass)
                      tokens-by-second-pass)]
       (or (= x y)
           (t/is (= [{:token :id} {:token :ty-id}] (drop-last (diff x y)))))))
    tokens-by-second-pass))

(def sample-result
  {:queens [{:token :let} {:token :var} {:token :id, :name "N"} {:token :assign} {:token :digits, :value "8"} {:token :type} {:token :ty-id, :name "myint"} {:token :equal} {:token :ty-id, :name "int"} {:token :type} {:token :ty-id, :name "intArray"} {:token :equal} {:token :array} {:token :of} {:token :ty-id, :name "myint"} {:token :var} {:token :id, :name "row"} {:token :assign} {:token :ty-id, :name "intArray"} {:token :open-bracket} {:token :id, :name "N"} {:token :close-bracket} {:token :of} {:token :digits, :value "0"} {:token :var} {:token :id, :name "col"} {:token :assign} {:token :ty-id, :name "intArray"} {:token :open-bracket} {:token :id, :name "N"} {:token :close-bracket} {:token :of} {:token :digits, :value "0"} {:token :var} {:token :id, :name "diag1"} {:token :assign} {:token :ty-id, :name "intArray"} {:token :open-bracket} {:token :id, :name "N"} {:token :plus} {:token :id, :name "N"} {:token :minus} {:token :digits, :value "1"} {:token :close-bracket} {:token :of} {:token :digits, :value "0"} {:token :var} {:token :id, :name "diag2"} {:token :assign} {:token :ty-id, :name "intArray"} {:token :open-bracket} {:token :id, :name "N"} {:token :plus} {:token :id, :name "N"} {:token :minus} {:token :digits, :value "1"} {:token :close-bracket} {:token :of} {:token :digits, :value "0"} {:token :function} {:token :id, :name "printboard"} {:token :open-paren} {:token :close-paren} {:token :equal} {:token :open-paren} {:token :for} {:token :id, :name "i"} {:token :assign} {:token :digits, :value "0"} {:token :to} {:token :id, :name "N"} {:token :minus} {:token :digits, :value "1"} {:token :do} {:token :open-paren} {:token :for} {:token :id, :name "j"} {:token :assign} {:token :digits, :value "0"} {:token :to} {:token :id, :name "N"} {:token :minus} {:token :digits, :value "1"} {:token :do} {:token :id, :name "print"} {:token :open-paren} {:token :if} {:token :id, :name "col"} {:token :open-bracket} {:token :id, :name "i"} {:token :close-bracket} {:token :equal} {:token :id, :name "j"} {:token :then} {:token :string, :value " O"} {:token :else} {:token :string, :value " ."} {:token :close-paren} {:token :semi-colon} {:token :id, :name "print"} {:token :open-paren} {:token :string, :value "\\n"} {:token :close-paren} {:token :close-paren} {:token :semi-colon} {:token :id, :name "print"} {:token :open-paren} {:token :string, :value "\\n"} {:token :close-paren} {:token :close-paren} {:token :function} {:token :id, :name "try"} {:token :open-paren} {:token :id, :name "c"} {:token :colon} {:token :ty-id, :name "myint"} {:token :close-paren} {:token :equal} {:token :if} {:token :id, :name "c"} {:token :equal} {:token :id, :name "N"} {:token :then} {:token :id, :name "printboard"} {:token :open-paren} {:token :close-paren} {:token :else} {:token :for} {:token :id, :name "r"} {:token :assign} {:token :digits, :value "0"} {:token :to} {:token :id, :name "N"} {:token :minus} {:token :digits, :value "1"} {:token :do} {:token :if} {:token :id, :name "row"} {:token :open-bracket} {:token :id, :name "r"} {:token :close-bracket} {:token :equal} {:token :digits, :value "0"} {:token :and} {:token :id, :name "diag1"} {:token :open-bracket} {:token :id, :name "r"} {:token :plus} {:token :id, :name "c"} {:token :close-bracket} {:token :equal} {:token :digits, :value "0"} {:token :and} {:token :id, :name "diag2"} {:token :open-bracket} {:token :id, :name "r"} {:token :plus} {:token :digits, :value "7"} {:token :minus} {:token :id, :name "c"} {:token :close-bracket} {:token :equal} {:token :digits, :value "0"} {:token :then} {:token :open-paren} {:token :id, :name "row"} {:token :open-bracket} {:token :id, :name "r"} {:token :close-bracket} {:token :assign} {:token :digits, :value "1"} {:token :semi-colon} {:token :id, :name "diag1"} {:token :open-bracket} {:token :id, :name "r"} {:token :plus} {:token :id, :name "c"} {:token :close-bracket} {:token :assign} {:token :digits, :value "1"} {:token :semi-colon} {:token :id, :name "diag2"} {:token :open-bracket} {:token :id, :name "r"} {:token :plus} {:token :digits, :value "7"} {:token :minus} {:token :id, :name "c"} {:token :close-bracket} {:token :assign} {:token :digits, :value "1"} {:token :semi-colon} {:token :id, :name "col"} {:token :open-bracket} {:token :id, :name "c"} {:token :close-bracket} {:token :assign} {:token :id, :name "r"} {:token :semi-colon} {:token :id, :name "try"} {:token :open-paren} {:token :id, :name "c"} {:token :plus} {:token :digits, :value "1"} {:token :close-paren} {:token :semi-colon} {:token :id, :name "row"} {:token :open-bracket} {:token :id, :name "r"} {:token :close-bracket} {:token :assign} {:token :digits, :value "0"} {:token :semi-colon} {:token :id, :name "diag1"} {:token :open-bracket} {:token :id, :name "r"} {:token :plus} {:token :id, :name "c"} {:token :close-bracket} {:token :assign} {:token :digits, :value "0"} {:token :semi-colon} {:token :id, :name "diag2"} {:token :open-bracket} {:token :id, :name "r"} {:token :plus} {:token :digits, :value "7"} {:token :minus} {:token :id, :name "c"} {:token :close-bracket} {:token :assign} {:token :digits, :value "0"} {:token :close-paren} {:token :in} {:token :id, :name "try"} {:token :open-paren} {:token :digits, :value "0"} {:token :close-paren} {:token :end}]

   :merge [{:token :let} {:token :type} {:token :ty-id, :name "any"} {:token :equal} {:token :open-brace} {:token :id, :name "any"} {:token :colon} {:token :ty-id, :name "int"} {:token :close-brace} {:token :var} {:token :id, :name "buffer"} {:token :assign} {:token :id, :name "getchar"} {:token :open-paren} {:token :close-paren} {:token :function} {:token :id, :name "readint"} {:token :open-paren} {:token :id, :name "any"} {:token :colon} {:token :ty-id, :name "any"} {:token :close-paren} {:token :colon} {:token :ty-id, :name "int"} {:token :equal} {:token :let} {:token :var} {:token :id, :name "i"} {:token :assign} {:token :digits, :value "0"} {:token :function} {:token :id, :name "isdigit"} {:token :open-paren} {:token :id, :name "s"} {:token :colon} {:token :ty-id, :name "string"} {:token :close-paren} {:token :colon} {:token :ty-id, :name "int"} {:token :equal} {:token :id, :name "ord"} {:token :open-paren} {:token :id, :name "buffer"} {:token :close-paren} {:token :geq} {:token :id, :name "ord"} {:token :open-paren} {:token :string, :value "0"} {:token :close-paren} {:token :and} {:token :id, :name "ord"} {:token :open-paren} {:token :id, :name "buffer"} {:token :close-paren} {:token :leq} {:token :id, :name "ord"} {:token :open-paren} {:token :string, :value "9"} {:token :close-paren} {:token :in} {:token :while} {:token :id, :name "buffer"} {:token :equal} {:token :string, :value " "} {:token :pipe} {:token :id, :name "buffer"} {:token :equal} {:token :string, :value "\\n"} {:token :do} {:token :id, :name "buffer"} {:token :assign} {:token :id, :name "getchar"} {:token :open-paren} {:token :close-paren} {:token :semi-colon} {:token :id, :name "any"} {:token :period} {:token :id, :name "any"} {:token :assign} {:token :id, :name "isdigit"} {:token :open-paren} {:token :id, :name "buffer"} {:token :close-paren} {:token :semi-colon} {:token :while} {:token :id, :name "isdigit"} {:token :open-paren} {:token :id, :name "buffer"} {:token :close-paren} {:token :do} {:token :open-paren} {:token :id, :name "i"} {:token :assign} {:token :id, :name "i"} {:token :star} {:token :digits, :value "10"} {:token :plus} {:token :id, :name "ord"} {:token :open-paren} {:token :id, :name "buffer"} {:token :close-paren} {:token :minus} {:token :id, :name "ord"} {:token :open-paren} {:token :string, :value "0"} {:token :close-paren} {:token :semi-colon} {:token :id, :name "buffer"} {:token :assign} {:token :id, :name "getchar"} {:token :open-paren} {:token :close-paren} {:token :close-paren} {:token :semi-colon} {:token :id, :name "i"} {:token :end} {:token :type} {:token :ty-id, :name "list"} {:token :equal} {:token :open-brace} {:token :id, :name "first"} {:token :colon} {:token :ty-id, :name "int"} {:token :comma} {:token :id, :name "rest"} {:token :colon} {:token :ty-id, :name "list"} {:token :close-brace} {:token :function} {:token :id, :name "readlist"} {:token :open-paren} {:token :close-paren} {:token :colon} {:token :ty-id, :name "list"} {:token :equal} {:token :let} {:token :var} {:token :id, :name "any"} {:token :assign} {:token :ty-id, :name "any"} {:token :open-brace} {:token :id, :name "any"} {:token :equal} {:token :digits, :value "0"} {:token :close-brace} {:token :var} {:token :id, :name "i"} {:token :assign} {:token :id, :name "readint"} {:token :open-paren} {:token :id, :name "any"} {:token :close-paren} {:token :in} {:token :if} {:token :id, :name "any"} {:token :period} {:token :id, :name "any"} {:token :then} {:token :ty-id, :name "list"} {:token :open-brace} {:token :id, :name "first"} {:token :equal} {:token :id, :name "i"} {:token :comma} {:token :id, :name "rest"} {:token :equal} {:token :id, :name "readlist"} {:token :open-paren} {:token :close-paren} {:token :close-brace} {:token :else} {:token :open-paren} {:token :id, :name "buffer"} {:token :assign} {:token :id, :name "getchar"} {:token :open-paren} {:token :close-paren} {:token :semi-colon} {:token :nil} {:token :close-paren} {:token :end} {:token :function} {:token :id, :name "merge"} {:token :open-paren} {:token :id, :name "a"} {:token :colon} {:token :ty-id, :name "list"} {:token :comma} {:token :id, :name "b"} {:token :colon} {:token :ty-id, :name "list"} {:token :close-paren} {:token :colon} {:token :ty-id, :name "list"} {:token :equal} {:token :if} {:token :id, :name "a"} {:token :equal} {:token :nil} {:token :then} {:token :id, :name "b"} {:token :else} {:token :if} {:token :id, :name "b"} {:token :equal} {:token :nil} {:token :then} {:token :id, :name "a"} {:token :else} {:token :if} {:token :id, :name "a"} {:token :period} {:token :id, :name "first"} {:token :lt} {:token :id, :name "b"} {:token :period} {:token :id, :name "first"} {:token :then} {:token :ty-id, :name "list"} {:token :open-brace} {:token :id, :name "first"} {:token :equal} {:token :id, :name "a"} {:token :period} {:token :id, :name "first"} {:token :comma} {:token :id, :name "rest"} {:token :equal} {:token :id, :name "merge"} {:token :open-paren} {:token :id, :name "a"} {:token :period} {:token :id, :name "rest"} {:token :comma} {:token :id, :name "b"} {:token :close-paren} {:token :close-brace} {:token :else} {:token :ty-id, :name "list"} {:token :open-brace} {:token :id, :name "first"} {:token :equal} {:token :id, :name "b"} {:token :period} {:token :id, :name "first"} {:token :comma} {:token :id, :name "rest"} {:token :equal} {:token :id, :name "merge"} {:token :open-paren} {:token :id, :name "a"} {:token :comma} {:token :id, :name "b"} {:token :period} {:token :id, :name "rest"} {:token :close-paren} {:token :close-brace} {:token :function} {:token :id, :name "printint"} {:token :open-paren} {:token :id, :name "i"} {:token :colon} {:token :ty-id, :name "int"} {:token :close-paren} {:token :equal} {:token :let} {:token :function} {:token :id, :name "f"} {:token :open-paren} {:token :id, :name "i"} {:token :colon} {:token :ty-id, :name "int"} {:token :close-paren} {:token :equal} {:token :if} {:token :id, :name "i"} {:token :gt} {:token :digits, :value "0"} {:token :then} {:token :open-paren} {:token :id, :name "f"} {:token :open-paren} {:token :id, :name "i"} {:token :slash} {:token :digits, :value "10"} {:token :close-paren} {:token :semi-colon} {:token :id, :name "print"} {:token :open-paren} {:token :id, :name "chr"} {:token :open-paren} {:token :id, :name "i"} {:token :minus} {:token :id, :name "i"} {:token :slash} {:token :digits, :value "10"} {:token :star} {:token :digits, :value "10"} {:token :plus} {:token :id, :name "ord"} {:token :open-paren} {:token :string, :value "0"} {:token :close-paren} {:token :close-paren} {:token :close-paren} {:token :close-paren} {:token :in} {:token :if} {:token :id, :name "i"} {:token :lt} {:token :digits, :value "0"} {:token :then} {:token :open-paren} {:token :id, :name "print"} {:token :open-paren} {:token :string, :value "-"} {:token :close-paren} {:token :semi-colon} {:token :id, :name "f"} {:token :open-paren} {:token :minus} {:token :id, :name "i"} {:token :close-paren} {:token :close-paren} {:token :else} {:token :if} {:token :id, :name "i"} {:token :gt} {:token :digits, :value "0"} {:token :then} {:token :id, :name "f"} {:token :open-paren} {:token :id, :name "i"} {:token :close-paren} {:token :else} {:token :id, :name "print"} {:token :open-paren} {:token :string, :value "0"} {:token :close-paren} {:token :end} {:token :function} {:token :id, :name "printlist"} {:token :open-paren} {:token :id, :name "l"} {:token :colon} {:token :ty-id, :name "list"} {:token :close-paren} {:token :equal} {:token :if} {:token :id, :name "l"} {:token :equal} {:token :nil} {:token :then} {:token :id, :name "print"} {:token :open-paren} {:token :string, :value "\\n"} {:token :close-paren} {:token :else} {:token :open-paren} {:token :id, :name "printint"} {:token :open-paren} {:token :id, :name "l"} {:token :period} {:token :id, :name "first"} {:token :close-paren} {:token :semi-colon} {:token :id, :name "print"} {:token :open-paren} {:token :string, :value " "} {:token :close-paren} {:token :semi-colon} {:token :id, :name "printlist"} {:token :open-paren} {:token :id, :name "l"} {:token :period} {:token :id, :name "rest"} {:token :close-paren} {:token :close-paren} {:token :in} {:token :id, :name "printlist"} {:token :open-paren} {:token :id, :name "merge"} {:token :open-paren} {:token :id, :name "readlist"} {:token :open-paren} {:token :close-paren} {:token :comma} {:token :id, :name "readlist"} {:token :open-paren} {:token :close-paren} {:token :close-paren} {:token :close-paren} {:token :end}]})
