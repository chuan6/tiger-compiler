(ns tokenizer
  (:require [clojure.string :as str]))

(def token-complex
  #{:id :comment :digits :string})

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
      (assert (empty? (clojure.set/intersection (set ids)
                                                (set kwords)))
              "ineffective test!")
      (doall
       (concat
        (for [id ids]
          (assert (= [(vec id) {:token :id :name id}]
                     (id-recognizer (seq id)))))
        (for [kw kwords]
          (assert (= [(vec kw) {:token (keyword kw)}]
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
              [t {:token kword}]
              [t {:token :id :name token}])))))))

(defn digits-recognizer
  {:test
   #(let [all-digits ["0" "1" "123" "123"]
          tail "f"
          with-non-digit-tail (map (fn [ds] (str ds tail)) all-digits)]
      (doall
       (concat
        (for [ds all-digits]
          (assert (= [(vec ds) {:token :digits :value ds}]
                     (digits-recognizer (seq ds)))))
        (for [ts with-non-digit-tail]
          (let [[s t] (digits-recognizer (seq ts))]
            (assert (= (without-prefix ts s) (vec tail)))
            (assert (= (str (:value t) tail) ts)))))))}
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
      (doall
       (concat
        (for [s strings]
          (assert (= [(vec s)
                      {:token :string :value (subs s 1 (dec (count s)))}]
                     (string-recognizer (seq s)))))
        (for [m missing-closing-quote]
          (assert (= [[]] (string-recognizer (seq m)))))
        (for [ts with-tail]
          (let [[s t] (string-recognizer (seq ts))]
            (assert (= (without-prefix ts s) (vec tail)))
            (assert (= (str \" (:value t) \" tail) ts)))))))}
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
      (doall
       (concat
        (for [cmt cmts]
          (assert (= [(vec cmt) {:token :comment :value cmt}]
                     (comment-recognizer (seq cmt)))))
        (for [m missing-closing]
          (assert (= [[]] (comment-recognizer (seq m)))))
        (for [ts with-tail]
          (let [[s t] (comment-recognizer (seq ts))]
            (assert (= (without-prefix ts s) (vec tail)))
            (assert (= (str (:value t) tail) ts)))))))}
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
      (doall
       (concat
        (for [p puncts]
          (assert (= [(vec p) {:token (token-punct (vec p))}]
                     (punct-recognizer (seq p)))))
        (for [w with-tail]
          (let [[s t] (punct-recognizer (seq w))]
            (assert (= (without-prefix w s) (vec tail)))
            (assert (= (:token t) (token-punct s))))))))}
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
                       pair)]
      (doall
       (for [pair variations]
         (let [test-str (str/join ((apply juxt pair) src))
               result (tokenize-str test-str)]
           (if (= (first pair) :illegal)
             (assert (= result empty-queue))
             (assert (= result
                        (map
                         (fn [k]
                           (cond-> {:token k}
                             (= k :id)      (assoc :name  (:id src))
                             (= k :string)  (assoc :value string-value)
                             (= k :digits)  (assoc :value (:digits src))
                             (= k :comment) (assoc :value (:comment src))))
                         (remove #{:spaces :illegal} pair)))))))))}
  [s]
  (assert (string? s))
  (let [inject (fn [f env]
                 (let [[s t] (f (:char-seq env))]
                   (cond-> (update env :char-seq without-prefix s)
                     t (update :token-seq conj t))))
        skip-spaces (fn [env]
                      (update env :char-seq
                              (partial drop-while
                                       #(Character/isWhitespace %))))
        puncts (set (seq ",:;()[]{}.+-*/=<>&|"))]
    (loop [curr-env {:char-seq s :token-seq empty-queue}]
      (let [{:keys [char-seq]
             :as no-leading-space-env} (skip-spaces curr-env)
            recognizer (let [[c c'] char-seq]
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
            next-env (inject recognizer no-leading-space-env)]
        (if (= (:char-seq next-env) char-seq) ;check if fixpoint is reached
          (:token-seq curr-env)
          (recur next-env))))))

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
      (doall
       (concat
        (for [v essential-forms]
          (assert (= (slot-to-ty-id v)
                     (norm-id-to-ty-id (slot-to-id v)))))
        (for [v broken-forms]
          (assert (= (slot-to-id v)
                     (norm-id-to-ty-id (slot-to-id v))))))))}
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
  (let [str (slurp path-to-file)
        ts (tokenize-str str)]
    (norm-id-to-ty-id ts)))
