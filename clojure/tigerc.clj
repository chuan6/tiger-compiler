(ns tiger.tokenizer
  (:require [clojure.string :as str]))

(def empty-string :ε)

(def slr-grammar
  {:terminals
   #{:array :break :do :else :end :for :function :if :in
     :let :nil :of :then :to :type :var :while
     :id :digits :string :ty-id ;:comment is omitted
     :comma :colon :semi-colon :open-paren :close-paren
     :open-bracket :close-bracket :open-brace :close-brace
     :period :assign :pipe :and
     :equal :gt :lt :diamond :leq :geq
     :minus :plus :star :slash empty-string}
   
   :start :expr

   :productions
   {:expr [[:val]
           [:lvalue :assign :expr]
           [:id :open-paren :close-paren]
           [:id :open-paren :expr-list :close-paren]
           [:open-paren :close-paren]
           [:ty-id :open-brace :close-brace]
           [:ty-id :open-brace :field-list :close-brace]
           [:ty-id :open-bracket :expr :close-bracket :of :expr]
           [:if :expr :then :expr :if-tail]
           [:while :expr :do :expr]
           [:for :id :assign :expr :to :expr :do :expr]
           [:break]
           [:let :decl-list :in :end]
           [:let :decl-list :in :expr-seq :end]]
    :if-tail [[empty-string] [:else :expr]]
    :lvalue [[:id] [:lvalue :period :id]
             [:lvalue :open-bracket :expr :close-bracket]]
    :expr-list [[:expr] [:expr-list :comma :expr]]
    :expr-seq [[:expr] [:expr-seq :semi-colon :expr]]
    :val [[:minus :val] [:arith]]
    :arith [[:arith :pipe :or-term] [:or-term]]
    :or-term [[:or-term :and :and-term] [:and-term]]
    :and-term [[:cmp-term :cmp :cmp-term] [:cmp-term]]
    :cmp-term [[:string] [:cmp-term :cal-0 :term] [:term]]
    :term [[:term :cal-1 :factor] [:factor]]
    :factor [[:digits] [:nil] [:lvalue]
             [:open-paren :expr-seq :close-paren]]
    :cmp [[:equal] [:lt] [:gt] [:leq] [:geq] [:diamond]]
    :cal-0 [[:plus] [:minus]]
    :cal-1 [[:star] [:slash]]
    :field-list [[:id :equal :expr] [:field-list :comma :id :equal :expr]]
    :decl-list [[:decl] [:decl-list :decl]]
    :decl [[:ty-decl] [:var-decl] [:fn-decl]]
    :ty-decl [[:type :ty-id :equal :ty]]
    :ty [[:ty-id]
         [:open-brace :close-brace]
         [:open-brace :ty-fields :close-brace]
         [:array :of :ty-id]]
    :ty-fields [[:ty-field] [:ty-fields :comma :ty-field]]
    :ty-field [[:id :colon :ty-id]]
    :var-decl [[:var :id :assign :expr] [:var :id :ty-id :assign :expr]]
    :fn-decl [[:function :id :open-paren :close-paren :equal :expr]
              [:function :id :open-paren :ty-fields :close-paren :equal :expr]
              [:function :id :open-paren :close-paren :colon :ty-id :equal :expr]
              [:function :id :open-paren :ty-fields :close-paren :colon :ty-id :equal :expr]]
    }})

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
                       (followed-by-brackets-then-of? i)))
            (recur (inc i) (assoc! v i {:token :ty-id :name (:name vi)}))
            (recur (inc i) v)))))))

(defn tokenize-file [path-to-file]
  (let [str (slurp path-to-file)
        tv (vec (tokenize-str str))]
    (norm-id-to-ty-id tv)))

(defn match-prod
  "return the matching production, and the matched vector of subtrees"
  [tree g]
  (let [pv (get (:productions g) (tree 0))
        n (count pv)
        cv (tree 1)
        len (count cv)]
    (loop [i 0] ;find from all productions of x the one that matches cv
      (assert (< i n))
      (let [p (pv i)]
        (if (and (= (count p) len) ;if lengths don't match, don't bother; "next!"
                 (loop [j 0]
                   (if (= j len) true
                       (let [a (cv j) b (p j)]
                         (if (vector? a) ;has subtree or is a leaf node
                           (if (= (a 0) b) (recur (inc j)) false)
                           (if (= (:token a) b) (recur (inc j)) false))))))
          {:nth i :children cv}
          (recur (inc i)))))))

(defn symtab-lookup [symtabv id]
  (let [n (count symtabv)]
    (loop [i (dec n)]
      (if (= i -1) nil
          (let [r (get (symtabv i) id)]
            (if r r
                (recur (dec i))))))))

(defn check [env tree]
  (apply (env (tree 0)) tree))

(defn scope [var-tab-stack type-tab-stack]
  (let [recur-check
        (fn [t] (check (scope var-tab-stack type-tab-stack) t))

        record?
        (fn [x] (not (nil? (:fields x))))

        array?
        (fn [x] (not (nil? (:elem-type x))))

        function?
        (fn [x] (not (nil? (:params x))))

        get-type
        (fn [env id]
          (-> id
              (symtab-lookup var-tab-stack)
              (symtab-lookup type-tab-stack)))]
    (fn [msg]
      (case msg
        :lvalue
        (fn [tree]
          (let [{i :nth cv :children} (match-prod tree)]
            (case i
              0 ;[:id]
              (symtab-lookup var-tab-stack
                             (symbol (:name (cv 0))))
              1 ;[:lvalue :period :id]
              (let [rec-type (check (scope var-tab-stack
                                           type-tab-stack)
                                    (cv 0))
                    rec-entry (symtab-lookup type-tab-stack rec-type)
                    fieldv (:fields rec-entry)
                    n (count fieldv)
                    target (symbol (:name (cv 2)))]
                (loop [i 0]
                  (assert (< i n))
                  (let [{name :name ty :type} (fieldv i)]
                    (if (= name target) ty
                        (recur (inc i))))))
              2 ;[:lvalue :open-bracket :expr :close-bracket]
              (let [arr-type (check (scope var-tab-stack
                                           type-tab-stack)
                                    (cv 0))
                    arr-entry (symtab-lookup type-tab-stack arr-type)]
                (assert arr-entry)
                (:elem-type arr-entry)))))
        :factor
        (fn [tree]
          (let [{i :nth cv :children} (match-prod tree)]
            (case i
              0 ;[:digits]
              'type-int
              1 ;[:nil]
              'type-nil
              2 ;[:lvalue]
              (recur-check (cv 0))
              3 ;;or [:open-paren :expr-seq :close-paren]
              (recur-check (cv 1)))))
        :expr-seq
        (fn [tree]
          (let [{i :nth cv :children} (match-prod tree)]
            (case i
              0 ;[:expr]
              (recur-check (cv 0))
              1 ;[:expr-seq :semi-colon :expr]
              (recur-check (cv 2)))))
        :term
        (fn [tree]
          (let [{i :nth cv :children} (match-prod tree)]
            (case i
              0 ;[:term :cal-1 :factor]
              (let [ta (recur-check (cv 0))
                    tb (recur-check (cv 2))]
                (assert (= 'type-int ta tb))
                'type-int)
              1 ;[:factor]
              (recur-check (cv 0)))))
        :cmp-term
        (fn [tree]
          (let [{i :nth cv :children} (match-prod tree)]
            (case i
              0 ;[:string]
              'type-str
              1 ;[:cmp-term :cal-0 :term]
              (let [ta (recur-check (cv 0))
                    tb (recur-check (cv 2))]
                (assert (= 'type-int ta tb))
                'type-int)
              2 ;[:factor]
              (recur-check (cv 0)))))
        :and-term
        (fn [tree]
          (let [{i :nth cv :children} (match-prod tree)]
            (case i
              0 ;[:cmp-term :cmp :cmp-term]
              (let [ta (recur-check (cv 0))
                    tb (recur-check (cv 2))]
                (assert (and (= ta tb) (#{'type-int 'type-str} ta)))
                'type-int)
              1 ;[:cmp-term]
              (recur-check (cv 0))
              )))
        :or-term
        (fn [tree]
          (let [{i :nth cv :children} (match-prod tree)]
            (case i
              0 ;[:or-term :and :and-term]
              (let [ta (recur-check (cv 0))
                    tb (recur-check (cv 2))]
                (assert (= 'type-int ta tb))
                'type-int)
              1 ;[:and-term]
              (recur-check (cv 0)))))
        :arith
        (fn [tree]
          (let [{i :nth cv :children} (match-prod tree)]
            (case i
              0 ;[:arith :pipe :or-term]
              (let [ta (recur-check (cv 0))
                    tb (recur-check (cv 2))]
                (assert (= 'type-int ta tb))
                'type-int)
              1 ;[:or-term]
              (recur-check (cv 0)))))
        :val
        (fn [tree]
          (let [{i :nth cv :children} (match-prod tree)]
            (case i
              0 ;[:minus :val]
              (let [ta (recur-check (cv 1))]
                (assert (= ta 'type-int))
                'type-int)
              1 ;[:arith]
              (recur-check (cv 0)))))
        :expr
        (fn [tree]
          (let [{i :nth cv :children} (match-prod tree)]
            (case i
              0 ;[:val]
              (recur-check (cv 0))
              1 ;[:lvalue :assign :expr]
              (let [ta (recur-check (cv 0))
                    tb (recur-check (cv 2))]
                (assert (or (= ta tb)
                            (and (= tb 'type-nil) (record? ta))))
                'type-void)
              2 ;[:id :open-paren :close-paren]
              (let [ta (get-type (:name (cv 0)))]
                (assert (and (function? ta) (empty? (:params ta))))
                (:ret-type ta))
              3 ;[:id :open-paren :expr-list :close-paren]
              (let [ta (get-type (:name (cv 0)))]
                (assert
                 (and (function? ta)
                      (let [pv (:params ta)]
                        (loop [i (dec (count pv))
                               av (cv 2)]
                          (assert (not (= i -1)))
                          (let [childv (av 1)]
                            (case (count childv)
                              1 ;[:expr]
                              (and (= i 0)
                                   (= (recur-check (childv 0)) (pv 0)))
                              3 ;[:expr-list :comma :expr]
                              (if (= (recur-check (childv 2)) (pv i))
                                (recur (dec i) (childv 0))
                                false)))))))
                (:ret-type ta))
              4 ;[:open-paren :close-paren]
              'type-void
              5 ;[:ty-id :open-brace :close-brace]
              (let [ta (symtab-lookup type-tab-stack (:name (cv 0)))]
                (assert (and (record? ta) (empty? (:fields ta))))
                (:id ta))
              6 ;[:ty-id :open-brace :field-list :close-brace]
              (let [ta (symtab-lookup type-tab-stack (:name (cv 0)))]
                (assert
                 (and (record? ta)
                      (let [fv (:fields ta) n (count fv)]
                        (loop [i (dec n)
                               av (cv 2)]
                          (assert (not (= i -1)))
                          (let [childv (av 1)]
                            (case (count childv)
                              3 ;[:id :equal :expr]
                              (and (= i 0)
                                   (let [{target-name :name target-type :type} (fv 0)]
                                     (and (= (:name (childv 0)) target-name)
                                          (= (recur-check (childv 2)) target-type))))
                              5 ;[:field-list :comma :id :equal :expr]
                              (let [{target-name :name target-type :type} (fv i)]
                                (if (and (= (:name (childv 0)) target-name)
                                         (= (recur-check (childv 2)) target-type))
                                  (recur (dec i) (childv 0))
                                  false))))))))
                (:id ta))
              7 ;[:ty-id :open-bracket :expr :close-bracket :of :expr]
              (let [ta (symtab-lookup type-tab-stack (cv 0))]
                (assert
                 (and (array? ta)
                      (= (recur-check (cv 2)) 'type-int)
                      (= (recur-check (cv 5)) (:elem-type ta))))
                (:id ta))
              8 ;[:if :expr :then :expr :if-tail]
              (do (assert (= (recur-check (cv 1)) 'type-int))
                  (let [else ((cv 4) 1)]
                    (if (empty? else)
                      'type-void
                      (let [ta (recur-check (cv 3))
                            tb (recur-check (else 1))]
                        (assert (= ta tb))
                        ta))))
              9 ;[:while :expr :do :expr]
              (let [ta (recur-check (cv 1))]
                (assert (= ta 'type-int))
                'type-void)
              10 ;[:for :id :assign :expr :to :expr :do :expr]
              (let [ta (recur-check (cv 3))
                    tb (recur-check (cv 5))]
                (assert (= 'type-int ta tb))
                'type-void)
              11 ;[:break]
              'type-void
              12 ;[:let :decl-list :in :end]
              'type-void
              13 ;[:let :decl-list :in :expr-seq :end]
              )))))))


