(ns cfg
  (:require [clojure.set :as set]))

(def empty-string :ε)
(def end-marker :$)

(def sample-cal
  {:terminals #{\+ \- \* \/ \( \) :num :ident}
   :start :goal
   :productions
   {:goal [[:expr]]
    :expr [[:expr \+ :term] [:expr \- :term] [:term]]
    :term [[:term \* :factor] [:term \/ :factor] [:factor]]
    :factor [[\( :expr \)] [:num] [:ident]]}})

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

(defn terminal? [grammar x]
  (if (or (= x empty-string) (= x end-marker))
    true
    (contains? (:terminals grammar) x)))

(declare first-set-non-term)

(defn first-set-production [g p s]
  (if (= p empty-string)
    #{empty-string}
    (if (empty? p)
      s
      (let [x (first p)]
        (if (terminal? g x)
          (conj s x)
          (let [r (first-set-non-term g x)
                ss (set/union s r)]
            (if (contains? r empty-string)
              (first-set-production g (rest p) ss)
              ss)))))))

(defn first-set-non-term [grammar nt]
  (let [right (get (:productions grammar) nt)
        n-alts (count right)]
    (loop [i   0
           tmp #{}]
      (if (= i n-alts)
        tmp
        (recur (inc i)
               (set/union tmp (first-set-production grammar (nth right i) #{})))))))

(defn first-set [grammar string]
  (first-set-production grammar string #{}))

;(def init-follow-set
 ; {:expr #{} :expr-helper #{}
  ; :term #{} :term-helper #{}
   ;:factor #{}})

(defn init-follow-set [grammar]
  (let [p (seq (:productions grammar))]
    (loop [result {}
           ps     p]
      (if (empty? ps)
        result
        (let [nt (nth (first ps) 0)]
          (recur (assoc result nt
                        (if (= nt (:start grammar))
                          #{end-marker} #{}))
                 (rest ps)))))))

(defn init-data [grammar]
  {:set (init-follow-set grammar)
   :infer (fn [x] x)})

(defn non-terminal? [grammar x]
  (let [ps (:productions grammar)]
    (not (nil? (get ps x)))))

(defn add-to-follow-set [s nt new]
  (assoc s nt (set/union (get s nt)
                         (disj new empty-string))))

(defn iterate-til-fixed [f x]
  (let [x' (f x)]
    (if (= x' x) x (iterate-til-fixed f x')))) ;powerful '=' operation!

(defn ff [f x y]
  (fn [s] (let [s (f s)]
               (assoc s y (set/union (get s x) (get s y))))))

(defn follow-set-production [grammar left right data]
  (loop [right right
         data data]
    (if (empty? right)
      data
      (let [x (first right)
            xs (rest right)]
        (cond
          (terminal? grammar x) (recur xs data)
          (non-terminal? grammar x)
          (let [x-next (first-set grammar xs)
                curr-set (add-to-follow-set (:set data) x x-next)]
              (if (or (empty? x-next) (contains? x-next empty-string))
                (recur xs
                       ;; add rule "FOLLOW(left) is a subset of FOLLOW(x)"
                       ;; to (:infer data). ff chains all the rules found,
                       ;; and will produce a final rule which is to be
                       ;; applied to iterate-til-fixed function.
                       {:set curr-set :infer (ff (:infer data) left x)})
                (recur xs
                       (assoc data :set curr-set))))
          ;;TODO :else
          )))))

(defn follow-set [grammar]
  (let [prods (seq (:productions grammar))]
    (loop [prods prods
           data (init-data grammar)]
      (if (empty? prods)
        (iterate-til-fixed (:infer data) (:set data))
        (recur (rest prods)
               (let [prod (first prods)
                     left (nth prod 0)]
                 (loop [alts (nth prod 1)
                        data data]
                   (if (empty? alts)
                     data
                     (let [right (first alts)]
                       (if (= right empty-string)
                         (recur (rest alts) data)
                         (recur (rest alts)
                                (follow-set-production grammar left right data))))))))))))

(def aug-start :S)
(defn aug-start-inv [g] (and (nil? (aug-start (:productions g)))
                             (nil? ((:terminals g) aug-start))))

(defn augment-grammar [g]
  (let [prod-dict (:productions g)]
    (assert (and (nil? (aug-start prod-dict)) (nil? ((:terminals g) aug-start))))
    (-> g
        (assoc :start aug-start)
        (assoc :productions (assoc prod-dict aug-start [[(:start g)]])))))

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
   (and (or (terminal? g x) (get (:productions g) x))
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

(def action-shift {:action :shift :state 0})
(def action-reduce {:action :reduce :production nil})
(def action-accept {:action :accept})
(def action-error {:action :error})

(defn consolidate-cc
  "Correspond each element of a canonical collection with a
  sequence number; support query by an element, and by
  a sequence number."
  [cc]
  (let [ccv (vec cc) n (count ccv)]
    {:by-x ccv
     :by-y (loop [ccm {} i 0]
             (if (= i n)
               ccm
               (recur (assoc ccm (ccv i) i)
                      (inc i))))}))

(defn items-by-state
  "get item set from consolidated canonical collection by state"
  [ccc state]
  (assert (>= state 0))
  (let [v (:by-x ccc) n (count v)]
    (if (< state n) (v state))))

(defn state-by-items
  "get state number from consolidated canonical collection by item set"
  [ccc items]
  (get (:by-y ccc) items))

(defn ccc-test [ccc]
  (let [{x :by-x y :by-y} ccc
        ks (keys y)]
    (loop [t (= (count ks) (count x))
           ks ks]
      (if (or (not t) (empty? ks))
        t
        (recur (let [k (first ks)]
                 (and t
                      (= k (->> k (state-by-items ccc)
                                (items-by-state ccc)))))
               (rest ks))))))

(defn slr-action-tab [g ccc]
  (let [terms      (seq (conj (:terminals g) end-marker))
        state      (fn [items] (state-by-items ccc items))
        items      (fn [state] (items-by-state ccc state))
        decode     (fn [item] (decode-lr-item item g))
        end?       (fn [item] (end-lr-item? item g))
        act-shift  (fn [state] (assoc action-shift :state state))
        act-reduce (fn [production] (assoc action-reduce :production production))
        act-accept action-accept
        act-error  action-error
        follow?    (let [flwset (follow-set g)]
                     (fn [a left] (contains? (get flwset left) a)))
        goto       (fn [its s] (lr-goto its s g))

        for-items
        (fn [its a] ;given items of the current state and a terminal
          (fn [act it]
            (let [act' (if (end? it)
                         (let [nt (:left it)]
                           (if (and (= nt aug-start) (= a end-marker))
                             act-accept
                             (if (follow? a nt)
                               (act-reduce (dissoc it :pos)))))
                         (if (= (decode it) a)
                           (act-shift (state (goto its a)))))]
              (if act'
                (if (or (nil? act) (= act' act))
                  act' (reduced (println "Inconsistency:" act' "with" act
                                         "at" "[" (state its) "," a  "]")))
                act))))

        for-states
        (fn [tab its]
          (assert (vector? tab))
          (loop [row {} ts terms]
            (if (empty? ts)
              (conj tab row)
              (let [t (first ts)]
                (recur
                 (assoc row t (reduce (for-items its t) nil (seq its)))
                 (rest ts))))))]
    (reduce for-states [] (:by-x ccc))))

(defn slr-goto-table [g ccc]
  (let [nterms (keys (:productions g))
        state (fn [items] (state-by-items ccc items))
        goto (fn [its s] (lr-goto its s g))

        for-states
        (fn [tab its]
          (assert (vector? tab))
          (loop [row {} nts nterms]
            (if (empty? nts)
              (conj tab row)
              (recur
               (let [nt (first nts)]
                 (assoc row nt (state (goto its nt))))
               (rest nts)))))]
    (reduce for-states [] (:by-x ccc))))

(defn construct-slr-table [g cc]
  ())
