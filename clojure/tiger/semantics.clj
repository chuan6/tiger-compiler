(ns semantics
  (:require [grammar :as gmr]))

(defn match-prod
  "return the matching production, and the matched vector of subtrees"
  [tree]
  (let [pv (get (:productions gmr/slr) (tree 0))
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

(declare scope)

(defn decl [var-tab-stack type-tab-stack]
  (let [recur-check (fn [t] (check (scope var-tab-stack type-tab-stack) t))
        get-type    (fn [name] (symtab-lookup type-tab-stack (symbol name)))
        cons-fieldv
        (fn [tree f]
          (assert (= (tree 0) :ty-fields))
          (let [subtreev (tree 1)]
            (case (count subtreev)
              1 ;[:ty-field]
              (let [cv ((subtreev 0) 1) ;[:id :colon :ty-id]
                    name (:name (cv 0))
                    type (get-type (:name (cv 2)))]
                [{:name name :type type}])
              3 ;[:ty-fields :comma :ty-field]
              (conj (f (subtreev 0) f) (f (subtreev 2) f)))))

        read-ty
        (fn [tree]
          (let [{i :nth cv :children} (match-prod tree)]
            (case i
              0 ;[:ty-id]
              (get-type (:name (cv 0)))
              1 ;[:open-brace :close-brace]
              {:fields []}
              2 ;[:open-brace :ty-fields :close-brace]
              {:fields (cons-fieldv (cv 1) cons-fieldv)}
              3 ;[:array :of :ty-id]
              {:elem-type (get-type (:name (cv 2)))}
              )))]
    (fn [msg]
      (case msg
        :ty-decl
        (fn [tree]
          (let [cv (tree 1)] ;[:type :ty-id :equal :ty]
            (conj type-tab-stack {(symbol (:name (cv 1))) (read-ty (cv 3))})))
        :var-decl
        (fn [tree]
          (let [{i :nth cv :children} (match-prod tree)]
            (case i
              0 ;[:var :id :assign :expr]
              (conj var-tab-stack {(symbol (:name (cv 1)))(recur-check (cv 3))})
              1 ;[:var :id :ty-id :assign :expr]
              (let [ta (recur-check (cv 4))]
                (assert (= (symbol (:name (cv 2))) ta))
                (conj var-tab-stack {(symbol (:name (cv 1))) ta}))
              )))
        :fn-decl
        (case i
          0 ;[:function :id :open-paren :close-paren :equal :expr]
          1 ;[:function :id :open-paren :ty-fields :close-paren :equal :expr]
          2 ;[:function :id :open-paren :close-paren :colon :ty-id :equal :expr]
          3 ;[:function :id :open-paren :ty-fields :close-paren :colon :ty-id :equal :expr]
          )))))

(defn scope [var-tab-stack type-tab-stack]
  (let [recur-check (fn [t] (check (scope var-tab-stack type-tab-stack) t))
        record?     (fn [x] (not (nil? (:fields x))))
        array?      (fn [x] (not (nil? (:elem-type x))))
        function?   (fn [x] (not (nil? (:params x))))
        get-type    (fn [env id]
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
              ()
              )))))))
