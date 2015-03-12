(ns parser.core
  (:require [clojure.edn :as edn]
            [instaparse.core :as insta]))

(def empty-string :ε)
(def end-string :$)

(def test-grammar
  {:terminals #{:plus :times :open-paren :close-paren :id}
   :start :e
   :productions
   {:e [[:e :plus :t] [:t]]
    :t [[:t :times :f] [:f]]
    :f [[:open-paren :e :close-paren] [:id]]}})

(def tiger-grammar
  {:terminals
   #{:array :break :do :else :end :for :function :if :in
     :let :nil :of :then :to :type :var :while
     :comma :colon :semi-colon :open-paren :close-paren
     :open-bracket :close-bracket :open-brace :close-brace
     :period :plus :minus :star :slash :equal :diamond :lt
     :leq :gt :geq :and :pipe :assign
     :string-constant :integer-constant
     :ty-id :id}
   :start :expr
   :productions
   {:expr
    [[:string-constant]
     [:integer-constant]
     [:nil]
     [:lvalue]
     [:minus :expr]
     [:expr :binop :expr]
     [:lvalue :assign :expr]
     [:id :open-paren :expr-list :close-paren]
     [:open-paren :expr-seq :close-paren]
     [:ty-id :open-brace :field-list :close-brace]
     [:ty-id :open-bracket :expr :close-bracket :of :expr]
     [:if :expr :then :expr]
     [:if :expr :then :expr :else :expr]
     [:while :expr :do :expr]
     [:for :id :assign :expr :to :expr :do :expr]
     [:break]
     [:let :decl-list :in :expr-seq :end]]

    :expr-seq
    [[empty-string]
     [:expr :expr-seq-tail]]
    :expr-seq-tail
    [[empty-string]
     [:semi-colon :expr :expr-seq-tail]]

    :expr-list
    [[empty-string]
     [:expr :expr-list-tail]]

    :expr-list-tail
    [[empty-string]
     [:comma :expr :expr-list-tail]]

    :field-list
    [[empty-string]
     [:id :equal :expr :field-list-tail]]

    :field-list-tail
    [[empty-string]
     [:comma :id :equal :expr :field-list-tail]]

    :lvalue
    [[:id :lvalue-tail]]

    :lvalue-tail
    [[empty-string]
     [:period :id :lvalue-tail]
     [:open-bracket :expr :close-bracket :lvalue-tail]]

    :binop
    [[:plus] [:minus] [:star] [:slash] [:equal] [:diamond] [:lt] [:gt] [:leq] [:geq] [:and] [:pipe]]

    :decl-list
    [[empty-string]
     [:decl :decl-list]]

    :decl
    [[:ty-decl] [:var-decl] [:fn-decl]]

    :ty-decl
    [[:type :ty-id :ty]]

    :ty
    [[:ty-id]
     [:open-brace :ty-fields :close-brace]
     [:array :of :ty-id]]

    :ty-fields
    [[empty-string]
     [:ty-field :ty-fields-tail]]

    :ty-fields-tail
    [[empty-string]
     [:comma :ty-field :ty-fields-tail]]

    :ty-field
    [[:id :colon :ty-id]]

    :var-decl
    [[:var :id :assign :expr]
     [:var :id :ty-id :assign :expr]]

    :fn-decl
    [[:function :id :open-paren :ty-fields :close-paren :equal :expr]
     [:function :id :open-paren :ty-fields :close-paren :colon :ty-id :equal :expr]]}})

(defn grammar-inv [g]
  "terminals found in :productions of the grammar equals its :terminals, or not"
  (let [target (:terminals g)
        prod-dict (:productions g)
        tset  (loop [ps (seq prod-dict)
                     ts #{}]
                (if (empty? ps)
                  ts
                  (recur
                   (rest ps)
                   (let [p (first ps)]
                     (loop [p-alts (seq (p 1))
                            ts ts]
                       (if (empty? p-alts)
                         ts
                         (recur
                          (rest p-alts)
                          (let [p-alt (first p-alts)]
                            (loop [p-seq (seq p-alt)
                                   ts ts]
                              (if (empty? p-seq)
                                ts
                                (recur
                                 (rest p-seq)
                                 (let [k (first p-seq)]
                                   (if (k prod-dict)
                                     ts
                                     (conj ts k))))))))))))))]
    (if (= target tset)
      (do (println "well defined.") true)
      (do (println "<" (clojure.set/difference target tset))
          (println ">" (clojure.set/difference tset target))
          false))))

(def parse-string
  (insta/parser
   "S = '\"' Q
    Q = '\"' | '\\\\' C | !('\"' | '\\\\') #'\\p{Print}' Q
    C = '\\\\' Q | !'\\\\' #'\\p{Print}' Q"))

(def parse-comment
  (insta/parser
   "S = '/*' R? S? R? '*/'
    R = #'\\p{Print}' | !'*/' #'\\p{Print}' #'\\p{Print}' | !'/*' #'\\p{Print}' #'\\p{Print}' R"))

(def aug-start :S)
(defn aug-start-inv [g] (and (nil? (aug-start (:productions g)))
                             (nil? ((:terminals g) aug-start))))

(defn augment-grammar [g]
  (let [prod-dict (:productions g)]
    (assert (and (nil? (aug-start prod-dict)) (nil? ((:terminals g) aug-start))))
    (-> g
        (assoc :start aug-start)
        (assoc :productions (assoc prod-dict aug-start [[(:start g) end-string]])))))

(def lr-item {:left aug-start :nth 0 :pos 0})

(defn valid-lr-item? [item-x g]
  (let [{nt :left x :nth y :pos} item-x
        prod-dict (:productions g)
        v (nt prod-dict)]
    (and v (>= x 0) (>= y 0) (< x (count v)) (<= y (count (v x))))))

;;expect valid item
(defn end-lr-item?
  "Is the item at the end of its production?"
  [item-x g]
  (let [{nt :left x :nth y :pos} item-x
        prod-dict (:productions g)
        n (count ((nt prod-dict) x))]
    (= n y)))

;;expect valid item
(defn decode-lr-item [item-x g]
  (let [{nt :left x :nth y :pos} item-x
        prod-dict (:productions g)]
    (((nt prod-dict) x) y)))

;;expect valid item
(defn forward-lr-item [item-x g]
  (let [{nt :left x :nth y :pos} item-x
        prod-dict (:productions g)
        limit (count ((nt prod-dict) x))
        y (inc y)]
    (if (<= y limit) (assoc item-x :pos y))))

(defn lr-closure [lr-item-set g]
  (assert ;every item is valid in g
   (loop [t true s (seq lr-item-set)]
     (if (empty? s) t
         (recur (and t (valid-lr-item? (first s) g))
                (rest s)))))
  (loop [cls #{} s (seq lr-item-set) done-set #{}]
    (if (empty? s)
      ;;add initial item set to closure in the end, to ensure that
      ;;done-set works as intended
      (clojure.set/union cls lr-item-set)
      (let [item-x (first s)]
        (if (end-lr-item? item-x g)
          (recur cls (rest s) done-set)
          (let [x (decode-lr-item item-x g)
                prod-dict (:productions g)
                v (x prod-dict)]
            (if (or (nil? v)
                    (done-set x))
              ;;either x is a terminal grammar symbol, or relevant items
              ;;of which :left is x has already been added to closure
              (recur cls (rest s) done-set)
              ;;otherwise, expand closure on x, and maybe further
              (let [item-x (assoc lr-item :left x)
                    n (count v)
                    [cls s] (loop [cls cls s (rest s) i 0]
                              (if (= i n)
                                [cls s]
                                (let [item-y (assoc item-x :nth i)
                                      y (decode-lr-item item-y g)]
                                  (recur (conj cls item-y)
                                         (if (y prod-dict) (conj s item-y) s)
                                         (inc i)))))]
                (recur cls s (conj done-set x))))))))))

(defn lr-goto [lr-item-set x g]
  (assert ;x is a grammar symbol of g, and every item in lr-item-set is valid
   (and (or ((:terminals g) x) (x (:productions g)))
        (loop [t true s (seq lr-item-set)]
          (if (empty? s) t
              (recur (and t (valid-lr-item? (first s) g))
                     (rest s))))))
  (let [lr-item-set (loop [r #{} s (seq lr-item-set)]
                      (if (empty? s) r
                          (recur
                           (let [item-y (first s)]
                             (if (end-lr-item? item-y g) r
                                 (let [y (decode-lr-item item-y g)]
                                   (if (not (= y x)) r
                                     (conj r (forward-lr-item item-y g))))))
                           (rest s))))]
    (lr-closure lr-item-set g)))

(defn list-grammar-symbols [g]
  (let [s (seq (:terminals g))]
    (concat s (keys (:productions g)))))

(defn iterate-til-fixed [f x]
  (let [x' (f x)]
    (if (= x' x) x (iterate-til-fixed f x')))) ;powerful '=' operation!

(defn canonical-coll [g]
  (let [g (augment-grammar g)
        symbols (list-grammar-symbols g)

        reducer-0 ;for each grammar symbol in grammar g
        (fn [lr-item-set]
          (fn [coll sym]
            (let [x (lr-goto lr-item-set sym g)]
              (if (or (empty? x) (contains? coll x))
                coll (conj coll x)))))

        reducer-1 ;for each item set in current collection
        (fn [coll lr-item-set]
          (reduce (reducer-0 lr-item-set) coll symbols))

        f
        (fn [coll]
          (reduce reducer-1 coll (seq coll)))

        coll #{(lr-closure #{{:left aug-start :nth 0 :pos 0}} g)}
        ]
    (iterate-til-fixed f coll)))

(defn tranform [t]
  (insta/transform {:exp (fn [e] e)
                    :int (fn [i] [:int (edn/read-string i)])
                    :vardec (fn [[:id x] e] [:vardec x e])
                    :tvardec (fn [[:id x] [:id t] e] [:tvardec x t e])} t))
