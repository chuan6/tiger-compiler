(ns tigerc.ast)

(defn trans-expr [nth cv]
  (case nth
    0 (cv 0)
    1 [:assign (cv 0) (cv 2)]
    2 [:empty]
    3 [:record (symbol (:name (cv 0))) []]
    4 [:record (symbol (:name (cv 0))) (cv 2)]
    5 [:array (symbol (:name (cv 0))) (cv 2) (cv 5)]
    6 (let [else (cv 4)]
        (if (nil? else)
          [:if (cv 1) (cv 3)]
          [:if (cv 1) (cv 3) else]))
    7 [:while (cv 1) (cv 3)]
    8 [:for (symbol (:name (cv 1))) (cv 3) (cv 5) (cv 7)]
    9 [:break]
    10 [:let (cv 1) []]
    11 [:let (cv 1) (cv 3)]))

(defn trans-if-tail [nth cv]
  (case nth 0 nil 1 (cv 1)))

(defn trans-lvalue [nth cv]
  (case nth
    0 [:lvalue :simple (symbol (:name (cv 0)))]
    1 [:lvalue :field (cv 0) (symbol (:name (cv 2)))]
    2 [:lvalue :subscript (cv 0) (cv 2)]))

(defn trans-expr-list [nth cv]
  (case nth 0 cv 1 (conj (cv 0) (cv 2))))

(defn trans-expr-seq [nth cv]
  (case nth 0 cv 1 (conj (cv 0) (cv 2))))

(defn trans-val [nth cv]
  (case nth 0 [:neg (cv 1)] 1 (cv 0)))

(defn trans-arith [nth cv]
  (case nth 0 [:or (cv 0) (cv 2)] 1 (cv 0)))

(defn trans-or-term [nth cv]
  (case nth 0 [:and (cv 0) (cv 2)] 1 (cv 0)))

(defn trans-and-term [nth cv]
  (case nth
    0 [:cmp (cv 1) (cv 0) (cv 2)]
    1 (cv 0)))

(defn trans-cmp-term [nth cv]
  (case nth
    0 [:string (:value (cv 0))]
    1 [:cal (cv 1) (cv 0) (cv 2)]
    2 (cv 0)))

(defn trans-term [nth cv]
  (case nth
    0 [:cal (cv 1) (cv 0) (cv 2)]
    1 (cv 0)))

(defn trans-factor [nth cv]
  (case nth
    0 [:int (Integer/parseInt (:value (cv 0)))]
    1 [:nil]
    2 (cv 0)
    3 [:seq (cv 1)]
    4 [:call (symbol (:name (cv 0))) []]
    5 [:call (symbol (:name (cv 0))) (cv 2)]))

(defn trans-cmp [nth cv]
  (case nth 0 :eq 1 :lt 2 :gt 3 :leq 4 :geq 5 :neq))

(defn trans-cal-0 [nth cv]
  (case nth 0 :add 1 :sub))

(defn trans-cal-1 [nth cv]
  (case nth 0 :mul 1 :div))

(defn trans-field-list [nth cv]
  (case nth
    0 [[(symbol (:name (cv 0))) (cv 2)]]
    1 (conj (cv 0) [(symbol (:name (cv 2))) (cv 4)])))

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

(defn trans-decl [nth cv] (cv 0))

(defn trans-ty-decl [nth cv]
  (case nth
    0 [:ty-decl (symbol (:name (cv 1))) (cv 3)]))

(defn trans-ty [nth cv]
  (case nth
    0 [:alias  (symbol (:name (cv 0)))]
    1 [:record []]
    2 [:record (cv 1)]
    3 [:array  (symbol (:name (cv 2)))]))

(defn trans-ty-fields [nth cv]
  (case nth 0 cv 1 (conj (cv 0) (cv 2))))

(defn trans-ty-field [nth cv]
  (case nth
    0 [(symbol (:name (cv 0))) (symbol (:name (cv 2)))]))

(defn trans-var-decl [nth cv]
  (case nth
    0 [:var-decl (symbol (:name (cv 1))) (cv 3)]
    1 [:var-decl (symbol (:name (cv 1))) (symbol (:name (cv 2))) (cv 4)]))

(defn trans-fn-decl [nth cv]
  (case nth
    0 [:fn-decl true (symbol (:name (cv 1))) [] (cv 5)] ;true for no return
    1 [:fn-decl true (symbol (:name (cv 1))) (cv 3) (cv 6)]
    2 [:fn-decl false (symbol (:name (cv 1))) [] (symbol (:name (cv 5))) (cv 7)]
    3 [:fn-decl false (symbol (:name (cv 1))) (cv 3) (symbol (:name (cv 6))) (cv 8)]))

;;;transform concrete syntax tree to abstract syntax tree
(defn slr-transform [p cv]
  (let [{nt :left i :nth} p
        f (case nt
            :expr trans-expr
            :if-tail trans-if-tail
            :lvalue trans-lvalue
            :expr-list trans-expr-list
            :expr-seq trans-expr-seq
            :val trans-val
            :arith trans-arith
            :or-term trans-or-term
            :and-term trans-and-term
            :cmp-term trans-cmp-term
            :term trans-term
            :factor trans-factor
            :cmp trans-cmp
            :cal-0 trans-cal-0
            :cal-1 trans-cal-1
            :field-list trans-field-list
            :decl-list trans-decl-list
            :decl trans-decl
            :ty-decl trans-ty-decl
            :ty trans-ty
            :ty-fields trans-ty-fields
            :ty-field trans-ty-field
            :var-decl trans-var-decl
            :fn-decl trans-fn-decl)]
    (f i cv)))

