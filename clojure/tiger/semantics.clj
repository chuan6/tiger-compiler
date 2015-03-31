(ns tiger.semantics)

(defn syntax-tree-inv [t])

(defn match-prod
  "return the matching production, and the matched vector of subtrees"
  [tree]
  (let [pv (get (:productions tiger/tokenizer/tiger-grammar-slr) (tree 0))
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

(def semantic-env {:var-tab-stack [] :ty-tab-stack []})

(defn semantic-env []
  (fn [msg]
    (case msg
      :push-type-tab
      :push-var-tab)))

(defn get-type [env id]
  (assert (symbol? id))
  (symtab-lookup (:var-tab-stack env) id))

(defn get-typedef [env ty-id]
  (assert (symbol? ty-id))
  (symtab-lookup (:ty-tab-stack env) ty-id))

(def array-typedef {:elem-type nil})
(def record-typedef {:fields []})

(def func-vardef {:params [] :ret-type 'type-void})
(def array-vardef {:size 0})

(declare typeof-lvalue)
(declare typeof-factor)
(declare typeof-expr-seq)
(declare typeof-term)
(declare typeof-cmp-term)
(declare typeof-and-term)
(declare typeof-or-term)
(declare typeof-arith)
(declare typeof-val)
(declare typeof-expr)


(defn typeof-lvalue [env t]
  (let [{i :nth cv :children} (match-prod t)]
    (case i
      0 ;[:id]
      (get-)
      (symtab-lookup (:var-tab-stack env) (:name (cv 0)))
      
      1 ;[:lvalue :period :id]
      (let [rec-type (typeof-lvalue env (cv 0))
            rec-entry (symtab-lookup (:ty-tab-stack env) rec-type)
            fieldv (:fields rec-entry)
            n (count fieldv)
            target (:name (cv 2))]
        (loop [i 0]
          (assert (< i n))
          (let [{name :name ty :type} (fieldv i)]
            (if (= name target) ty
                (recur (inc i))))))
      
      2 ;[:lvalue :open-bracket :expr :close-bracket]
      (let [arr-type (typeof-lvalue env (cv 0))
            arr-entry (symtab-lookup (:ty-tab-stack env) arr-type)]
        (:elem-type arr-entry)))))

(defn typeof-factor [env t]
  (let [{i :nth cv :children} (match-prod t)]
    (case i
      0 ;[:digits]
      'type-int

      1 ;[:nil]
      'type-nil

      2 ;[:lvalue]
      (typeof-lvalue env (cv 0))

      3 ;[:open-paren :expr-seq :close-paren]
      (typeof-expr-seq env (cv 1)))))

(defn typeof-expr-seq [env t]
  (let [{i :nth cv :children} (match-prod t)]
    (case i
      0 ;[:expr]
      (typeof-expr env (cv 0))

      1 ;[:expr-seq :semi-colon :expr]
      (typeof-expr env (cv 2)))))

(defn typeof-term [env t]
  (let [{i :nth cv :children} (match-prod t)]
    (case i
      0 ;[:term :cal-1 :factor]
      (do (assert (= (typeof-term env (cv 0)) 'type-int))
          (assert (= (typeof-factor env (cv 2)) 'type-int))
          'type-int)

      1 ;[:factor]
      (typeof-factor env (cv 0)))))

(defn typeof-cmp-term [env t]
  (let [{i :nth cv :children} (match-prod t)]
    (case i
      0 ;[:string]
      'type-str

      1 ;[:cmp-term :cal-0 :term]
      (do (assert (= (typeof-cmp-term env (cv 0)) 'type-int))
          (assert (= (typeof-term env (cv 2)) 'type-int))
          'type-int)

      2 ;[:factor]
      (typeof-factor env (cv 0)))))

(defn typeof-and-term [env t]
  (let [{i :nth cv :children} (match-prod t)]
    (case i
      0 ;[:cmp-term :cmp :cmp-term]
      (let [ta (typeof-cmp-term env (cv 0))
            tb (typeof-cmp-term env (cv 2))]
        (assert (and (= ta tb)
                     (or (= ta 'type-int) (= ta 'type-str))))
        ta)

      1 ;[:cmp-term]
      (typeof-cmp-term env (cv 0)))))

(defn typeof-or-term [env t]
  (let [{i :nth cv :children} (match-prod t)]
    (case i
      0 ;[:or-term :and :and-term]
      (let [ta (typeof-or-term env (cv 0))
            tb (typeof-and-term env (cv 2))]
        (assert (= ta tb 'type-int))
        'type-int)

      1 ;[:and]
      (typeof-and-term env (cv 0)))))

(defn typeof-arith [env t]
  (let [{i :nth cv :children} (match-prod t)]
    (case i
      0 ;[:arith :pipe :or-term]
      (let [ta (typeof-arith env (cv 0))
            tb (typeof-or-term env (cv 2))]
        (assert (= ta tb 'type-int))
        'type-int)

      1 ;[:or-term]
      (typeof-or-term env (cv 0)))))

(defn typeof-val [env t]
  (let [{i :nth cv :children} (match-prod t)]
    (case i
      0 ;[:minus :val]
      (let [ta (typeof-val env (cv 1))]
        (assert (= ta 'type-int))
        'type-int)

      1 ;[:arith]
      (typeof-arith env (cv 0)))))

(defn typeof-expr [env t]
  (let [record?
        (fn [x] (not (nil? (:fields x))))

        array?
        (fn [x] (not (nil? (:elem-type x))))

        function?
        (fn [x] (not (nil? (:params x))))

        get-type
        (fn [env id]
          (-> id
              (symtab-lookup (:var-tab-stack env))
              (symtab-lookup (:ty-tab-stack env))))

        update-env
        (fn [env decl-list]
          ()) ;TODO

        {i :nth cv :children} (match-prod t)]
    (case i
      0 ;[:val]
      (typeof-val env (cv 0))

      1 ;[:lvalue :assign :expr]
      (let [ta (typeof-lvalue (cv 0))
            tb (typeof-expr (cv 2))]
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
                       av (cv 2)] ;:expr-list [[:expr] [:expr-list :comma :expr]]
                  (assert (not (= i -1)))
                  (let [childv (av 1)]
                    (case (count childv)
                      1 ;[:expr]
                      (and (= i 0)
                           (= (typeof-expr env (childv 0)) (pv 0)))
                      
                      3 ;[:expr-list :comma :expr]
                      (if (= (typeof-expr env (childv 2)) (pv i))
                        (recur (dec i) (childv 0))
                        false)))))))
        (:ret-type ta))

      4 ;[:open-paren :close-paren]
      'type-void

      5 ;[:ty-id :open-brace :close-brace]
      (let [ta (symtab-lookup (:ty-tab-stack env) (:name (cv 0)))]
        (assert (and (record? ta) (empty? (:fields ta))))
        (:id ta))

      6 ;[:ty-id :open-brace :field-list :close-brace]
      (let [ta (symtab-lookup (:ty-tab-stack env) (:name (cv 0)))]
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
                                  (= (typeof-expr env (childv 2)) target-type))))

                      5 ;[:field-list :comma :id :equal :expr]
                      (let [{target-name :name target-type :type} (fv i)]
                        (if (and (= (:name (childv 0)) target-name)
                                 (= (typeof-expr env (childv 2)) target-type))
                          (recur (dec i) (childv 0))
                          false))
                      ))))))
        (:id ta))

      7 ;[:ty-id :open-bracket :expr :close-bracket :of :expr]
      (let [ta (symtab-lookup (:ty-tab-stack env) (cv 0))]
        (assert
         (and (array? ta)
              (= (typeof-expr env (cv 2)) 'type-int)
              (= (typeof-expr env (cv 5)) (:elem-type ta))))
        (:id ta))

      8 ;[:if :expr :then :expr :if-tail]
      (do (assert (= (typeof-expr env (cv 1)) 'type-int))
          (let [else ((cv 4) 1)]
            (if (empty? else)
              'type-void
              (let [ta (typeof-expr env (cv 3))
                    tb (typeof-expr env (else 1))]
                (assert (= ta tb))
                ta))))

      9 ;[:while :expr :do :expr]
      'type-void

      10 ;[:for :id :assign :expr :to :expr :do :expr]
      'type-void
      
      11 ;[:break] TODO :break may need special check
      'type-void

      12 ;[:let :decl-list :in :end]
      'type-void

      13 ;[:let :decl-list :in :expr-seq :end]
      (typeof-expr-seq (update-env (cv 1)) (cv 3))
      )))
