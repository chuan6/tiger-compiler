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

(defn prod-vec
  "turn production dictionary of a grammar into vector of productions"
  [g]
  (let [prod-map (:productions g)]
    (loop [xs (keys prod-map)
           pset #{}]
      (if (empty? xs)
        (vec pset)
        (recur
         (rest xs)
         (let [x (first xs)
               pvec (x prod-map)
               n (count pvec)]
           (loop [i 0 pset pset]
             (if (= i n)
               pset
               (recur (inc i)
                      (conj pset (conj [x] (pvec i))))))))))))
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
    (and v (>= x 0) (>= y 0) (< x (count v)) (< y (count (v x))))))

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
    (if (< y limit) (assoc item-x :pos y))))

(defn lr-closure [lr-item-set g]
  (assert ;every item is valid in g
   (loop [t true s (seq lr-item-set)]
     (if (empty? s) t
         (recur (and t (valid-lr-item? (first s) g))
                (rest s)))))
  (loop [cls #{} s (seq lr-item-set) done-set #{}]
    (if (empty? s)
      (clojure.set/union cls lr-item-set)
      (let [x (decode-lr-item (first s) g)
            prod-dict (:productions g)
            v (x prod-dict)]
        (if (or (nil? v) (done-set x))
          (recur cls (rest s) done-set)
          (let [item-x (assoc lr-item :left x)
                n (count v)
                [cls s] (loop [cls cls s (rest s) i 0]
                          (if (= i n)
                            [cls s]
                            (let [item-y (assoc item-x :nth i)
                                  y (decode-lr-item item-y g)]
                              (if (y prod-dict) ;if item-y is a non-terminal,
                                ;;add it to s, instead of adding it to cls directly
                                (recur (conj cls item-y) (conj s item-y) (inc i))
                                ;;otherwise, add it to cls
                                (recur (conj cls item-y) s (inc i))))))]
            (recur cls s (conj done-set x))))))))

(defn tranform [t]
  (insta/transform {:exp (fn [e] e)
                    :int (fn [i] [:int (edn/read-string i)])
                    :vardec (fn [[:id x] e] [:vardec x e])
                    :tvardec (fn [[:id x] [:id t] e] [:tvardec x t e])} t))
