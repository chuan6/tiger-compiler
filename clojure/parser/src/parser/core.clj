(ns parser.core
  (:require [clojure.edn :as edn]
            [instaparse.core :as insta]))

(def empty-string :ε)

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
    [empty-string
     [:expr :expr-seq-tail]]

    :expr-seq-tail
    [empty-string
     [:semi-colon :expr :expr-seq-tail]]

    :expr-list
    [empty-string
     [:expr :expr-list-tail]]

    :expr-list-tail
    [empty-string
     [:comma :expr :expr-list-tail]]

    :field-list
    [empty-string
     [:id :equal :expr :field-list-tail]]

    :field-list-tail
    [empty-string
     [:comma :id :equal :expr :field-list-tail]]

    :lvalue
    [[:id :lvalue-tail]]

    :lvalue-tail
    [empty-string
     [:period :id :lvalue-tail]
     [:open-bracket :expr :close-bracket :lvalue-tail]]

    :binop
    [[:plus] [:minus] [:star] [:slash] [:equal] [:diamond] [:lt] [:gt] [:leq] [:geq] [:and] [:pipe]]

    :decl-list
    [empty-string
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
    [empty-string
     [:ty-field :ty-fields-tail]]

    :ty-fields-tail
    [empty-string
     [:comma :ty-field :ty-fields-tail]]

    :ty-field
    [[:id :colon :ty-id]]

    :var-decl
    [[:var :id :assign :expr]
     [:var :id :ty-id :assign :expr]]

    :fn-decl
    [[:function :id :open-paren :ty-fields :close-paren :equal :expr]
     [:function :id :open-paren :ty-fields :close-paren :colon :ty-id :equal :expr]]}})

(defn verify [grammar]
  "terminals found in :productions of the grammar equals its :terminals, or not"
  (let [target (:terminals grammar)
        prod-dict (:productions grammar)
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
                            (if (= p-alt empty-string)
                              ts
                              (loop [p-seq (seq p-alt)
                                     ts ts]
                                (if (empty? p-seq)
                                  ts
                                  (recur
                                   (rest p-seq)
                                   (let [k (first p-seq)]
                                     (if (k prod-dict)
                                       ts
                                       (conj ts k)))))))))))))))]
    (if (= target tset)
      (do (println "well defined.") true)
      (do (println "<" (clojure.set/difference target tset))
          (println ">" (clojure.set/difference tset target))
          false))))


(defn tranform [t]
  (insta/transform {:exp (fn [e] e)
                    :int (fn [i] [:int (edn/read-string i)])
                    :vardec (fn [[:id x] e] [:vardec x e])
                    :tvardec (fn [[:id x] [:id t] e] [:tvardec x t e])} t))
