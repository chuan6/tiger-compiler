(ns ast)

(defn trans-expr [nth cv]
  (case nth
    0 ; :val
    (cv 0)
    
    1 ; :lvalue :assign :expr
    [:assign (cv 0) (cv 2)]
    
    2 ; :open-paren :close-paren
    [:empty]
    
    3 ; :ty-id :open-brace :close-brace
    [:create-tmp (symbol (:name (cv 0)))]
    
    4 ; :ty-id :open-brace :field-list :close-brace
    [:create-tmp (symbol (:name (cv 0))) (cv 2)]

    5 ; :ty-id :open-bracket :expr :close-bracket :of :expr
    [:create-tmp (symbol (:name (cv 0))) (cv 2) (cv 5)]

    6 ; :if :expr :then :expr :if-tail
    (let [else (cv 4)]
      (if (nil? else)
        [:if (cv 1) (cv 3)]
        [:if (cv 1) (cv 3) else]))

    7 ; :while :expr :do :expr
    [:while (cv 1) (cv 3)]

    8 ; :for :id :assign :expr :to :expr :do :expr
    [:for (symbol (:name (cv 1))) (cv 3) (cv 5) (cv 7)]

    9 ; :break
    [:break] ;TODO need to ensure that the break is enclosed in a while/for expr

    10 ; :let :decl-list :in :end
    [:let (cv 1)]

    11 ; :let :decl-list :in :expr-seq :end
    [:let (cv 1) (cv 3)]))

(defn trans-if-tail [nth cv]
  (case nth
    0 nil ; empty-string
    1 (cv 1) ; :else :expr
    ))

(defn trans-lvalue [nth cv]
  (case nth
    0 [:lvalue :simple (symbol (:name (cv 0)))] ; :id
    1 [:lvalue :field (cv 0) (symbol (:name (cv 2)))]; :lvalue :period :id
    2 [:lvalue :subscript (cv 0) (cv 2)] ; :lvalue :open-bracket :expr :close-bracket
    ))

(defn trans-expr-list [nth cv]
  (case nth
    0 cv ; :expr
    1 (conj (cv 0) (cv 2)) ; :expr-list :comma :expr
    ))

(defn trans-expr-seq [nth cv]
  (case nth
    0 [:exprs (cv 0)] ; :expr
    1 (conj (cv 0) (cv 2)) ; :expr-seq :semi-colon :expr
    ))

(defn trans-val [nth cv]
  (case nth
    0 [:neg (cv 1)] ; :minus :val -> :int-neg
    1 (cv 0) ; :arith
    ))

(defn trans-arith [nth cv]
  (case nth
    0 [:or (cv 0) (cv 2)] ; :arith :pipe :or-term
    1 (cv 0) ; :or-term
    ))

(defn trans-or-term [nth cv]
  (case nth
    0 [:and (cv 0) (cv 2)] ; :or-term :and :and-term
    1 (cv 0) ; :and-term
    ))

(defn trans-and-term [nth cv]
  (case nth
    0 [:cmp (cv 1) (cv 0) (cv 2)] ; :cmp-term :cmp :cmp-term
    1 (cv 0) ; :cmp-term
    ))

(defn trans-cmp-term [nth cv]
  (case nth
    0 [:string (:value (cv 0))] ; :string
    1 [:cal (cv 1) (cv 0) (cv 2)] ; :cmp-term :cal-0 :term
    2 (cv 0) ; :term
    ))

(defn trans-term [nth cv]
  (case nth
    0 [:cal (cv 1) (cv 0) (cv 2)] ; :term :cal-1 :factor
    1 (cv 0) ; :factor
    ))

(defn trans-factor [nth cv]
  (case nth
    0 [:int (Integer/parseInt (:value (cv 0)))] ; :digits
    1 [:nil] ; :nil
    2 (cv 0) ; :lvalue
    3 (cv 1) ; :open-paren :expr-seq :close-paren
    4 ; :id :open-paren :close-paren
    [:call (symbol (:name (cv 0)))]
    
    5 ; :id :open-paren :expr-list :close-paren
    [:call (symbol (:name (cv 0))) (cv 2)]
    ))

(defn trans-cmp [nth cv]
  (case nth
    0 :eq ; :equal
    1 :lt ; :lt
    2 :gt ; :gt
    3 :leq ; :leq
    4 :geq ; :geq
    5 :neq ; :diamond
    ))

(defn trans-cal-0 [nth cv]
  (case nth
    0 :add ; :plus
    1 :sub ; :minus
    ))

(defn trans-cal-1 [nth cv]
  (case nth
    0 :mul ; :star
    1 :div ; :slash
    ))

(defn trans-field-list [nth cv]
  (case nth
    0 ; :id :equal :expr
    [:assign-fields [(symbol (:name (cv 0))) (cv 2)]]
    
    1 ; :field-list :comma :id :equal :expr
    (conj (cv 0) [(symbol (:name (cv 2))) (cv 4)])))

(defn trans-decl-list [nth cv]
  (case nth
    0 ; :decl
    (case ((cv 0) 0)
      :ty-decl [[:consec-ty-decl (cv 0)]]
      :var-decl cv
      :fn-decl [[:consec-fn-decl (cv 0)]])
    
    1 ; :decl-list :decl
    (let [prev (cv 0) curr (peek prev)
          next (cv 1) next-type (next 0)]
      (if (= next-type :var-decl)
        (conj prev next)
        (case (curr 0)
          :consec-ty-decl
          (case (next 0)
            :ty-decl (conj (pop prev) (conj curr next))
            :fn-decl (conj prev [:consec-fn-decl next]))

          :consec-fn-decl
          (case (next 0)
            :ty-decl (conj prev [:consec-ty-decl next])
            :fn-decl (conj (pop prev) (conj curr next)))

          (case (next 0)
            :ty-decl (conj prev [:consec-ty-decl next])
            :fn-decl (conj prev [:consec-fn-decl next])))))))

(defn trans-decl [nth cv]
  (case nth
    0 (cv 0) ; :ty-decl
    1 (cv 0) ; :var-decl
    2 (cv 0) ; :fn-decl
    ))

(defn trans-ty-decl [nth cv]
  (case nth
    0 ; :type :ty-id :equal :ty
    [:ty-decl (symbol (:name (cv 1))) (cv 3)]))

(defn trans-ty [nth cv]
  (case nth
    0 [:create-ty :alias (symbol (:name (cv 0)))] ; :ty-id
    1 [:create-ty :record []] ; :open-brace :close-brace
    2 [:create-ty :record (cv 1)] ; :open-brace :ty-fields :close-brace
    3 [:create-ty :array (symbol (:name (cv 2)))] ; :array :of :ty-id
    ))

(defn trans-ty-fields [nth cv]
  (case nth
    0 cv ; :ty-field
    1 (conj (cv 0) (cv 2)) ; :ty-fields :comma :ty-field
    ))

(defn trans-ty-field [nth cv]
  (case nth
    0 ; :id :colon :ty-id
    [:ty-assoc (symbol (:name (cv 0))) (symbol (:name (cv 2)))]))

(defn trans-var-decl [nth cv]
  (case nth
    0 ; :var :id :assign :expr
    [:var-decl (symbol (:name (cv 1))) (cv 3)]
    1 ; :var :id :ty-id :assign :expr
    [:var-decl (symbol (:name (cv 1))) (symbol (:name (cv 2))) (cv 4)]
    ))

(defn trans-fn-decl [nth cv]
  (case nth
    0 ; :function :id :open-paren :close-paren :equal :expr
    [:fn-decl true (symbol (:name (cv 1))) (cv 5)] ;true for no return
    1 ; :function :id :open-paren :ty-fields :close-paren :equal :expr
    [:fn-decl true (symbol (:name (cv 1))) (cv 3) (cv 6)]
    2 ; :function :id :open-paren :close-paren :colon :ty-id :equal :expr
    [:fn-decl false (symbol (:name (cv 1))) (symbol (:name (cv 5))) (cv 7)]
    3 ; :function :id :open-paren :ty-fields :close-paren :colon :ty-id :equal :expr
    [:fn-decl false (symbol (:name (cv 1))) (cv 3) (symbol (:name (cv 6))) (cv 8)]
  ))

;;;transform concrete syntax tree to abstract syntax tree
(defn slr-transform [p cv]
  (let [{nt :left i :nth} p]
    (case nt
      :expr       (trans-expr i cv)
      :if-tail    (trans-if-tail i cv)
      :lvalue     (trans-lvalue i cv)
      :expr-list  (trans-expr-list i cv)
      :expr-seq   (trans-expr-seq i cv)
      :val        (trans-val i cv)
      :arith      (trans-arith i cv)
      :or-term    (trans-or-term i cv)
      :and-term   (trans-and-term i cv)
      :cmp-term   (trans-cmp-term i cv)
      :term       (trans-term i cv)
      :factor     (trans-factor i cv)
      :cmp        (trans-cmp i cv)
      :cal-0      (trans-cal-0 i cv)
      :cal-1      (trans-cal-1 i cv)
      :field-list (trans-field-list i cv)
      :decl-list  (trans-decl-list i cv)
      :decl       (trans-decl i cv)
      :ty-decl    (trans-ty-decl i cv)
      :ty         (trans-ty i cv)
      :ty-fields  (trans-ty-fields i cv)
      :ty-field   (trans-ty-field i cv)
      :var-decl   (trans-var-decl i cv)
      :fn-decl    (trans-fn-decl i cv))))
