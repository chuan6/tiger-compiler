(ns parser
  (:require [cfg :refer :all]
            [clojure.set :as set]
            [clojure.test :as t]
            [tigerc.test :as tt]
            [tigerc.grammar :as tg]))

(def action-shift {:action :shift :state 0})
(def action-reduce {:action :reduce :production nil})
(def action-accept {:action :accept})
(def action-error {:action :error})

(defn grammar-object [g]
  (let [g (augment-grammar g)]
    {:grammar (delay g)
     :state-items-mappings (delay (indexed-canonical-coll (canonical-coll g)))
     :follow-set (delay (follow-set g))
     :goto (delay (partial lr-goto g))
     :decode-item (delay (partial decode-lr-item g))
     :end-position-item? (delay (partial end-position-lr-item? g))}))

(defn item-action-type
  {:test
   #(let [f (partial item-action-type (grammar-object if-grammar))]
      (tt/comprehend-tests
       (t/is (nil? (f {:left :e :nth 0 :pos 0} :then)))
       (t/is (nil? (f {:left :e :nth 0 :pos 4} :if)))
       (t/is (= action-shift (f {:left :e :nth 0 :pos 0} :if)))
       (t/is (= action-shift (f {:left :e :nth 0 :pos 2} :then)))
       (t/is (= action-accept (f {:left aug-start :nth 0 :pos 1} end-marker)))
       (t/is (= action-reduce (f {:left :e :nth 0 :pos 4} :then)))
       (t/is (= action-reduce (f {:left :e :nth 0 :pos 4} end-marker)))))}
  [gobj item t]
  (let [{:keys [decode-item end-position-item? follow-set]} gobj
        nt (:left item)]
    (cond (= (@decode-item item) t)
          action-shift

          (@end-position-item? item)
          (cond (and (= nt aug-start) (= t end-marker))
                action-accept

                (contains? (@follow-set nt) t)
                action-reduce))))

(defn resolve-actions
  {:test
   #(let [shift action-shift
          shift' (update shift :state inc)]
      (tt/comprehend-tests
       (t/is (nil? (resolve-actions false #{})))
       (t/is (= action-accept (resolve-actions false #{action-accept})))
       (t/is (= shift (resolve-actions true #{shift action-reduce})))
       (t/is (= :unresolved (resolve-actions false #{shift action-reduce})))
       (t/is (= :unresolved (resolve-actions false #{shift shift'})))
       (t/is (= :unresolved (resolve-actions true #{shift shift'})))))}
  [prefer-shift? actions]
  (let [shift-actions (delay (set/select #(= (:action %) :shift) actions))]
    (cond (empty? actions)
          nil

          (= (count actions) 1)
          (first actions)

          (and prefer-shift? (= (count @shift-actions) 1))
          (first @shift-actions)

          :else
          :unresolved)))

(def ^:private least-attempt-resolving (partial resolve-actions false))

(defn- slr-action [{:keys [goto state-items-mappings] :as gobj}
                   resolve-fn
                   state
                   t] 
  (let [{:keys [state->items items->state]} @state-items-mappings
        items (state->items state)
        item-action (fn [{nt :left x :nth :as item}]
                      (let [r (item-action-type gobj item t)]
                        (case (:action r)
                          :shift (assoc r :state (items->state (@goto items t)))
                          :accept r
                          :reduce (assoc r :production {:left nt :nth x})
                          nil)))
        actions (-> item-action (map items) set (disj nil))
        action (resolve-fn actions)]
    (if (= action :unresolved)
      (println "Unresolvable inconsistency found within actions:"
               actions "at [" state "," t "].")
      action)))

;;expect augmented grammar
(defn slr-action-tab [{:keys [state-items-mappings grammar] :as gobj}
                      resolve-fn]
  (let [tab-cells (for [state (keys (:state->items @state-items-mappings))
                        t (seq (conj (:terminals @grammar) end-marker))]
                    [state t])]
    (reduce
     (fn [ret [state t]]
       (assoc-in ret [state t] (slr-action gobj resolve-fn state t)))
     {} tab-cells)))

(defn- slr-goto [{:keys [goto state-items-mappings]}
                 state nt]
  (let [{:keys [state->items items->state]} @state-items-mappings]
    (-> state
        state->items
        (@goto nt)
        items->state)))

(defn slr-goto-tab [{:keys [grammar state-items-mappings] :as gobj}]
  (let [tab-cells (for [state (keys (:state->items @state-items-mappings))
                        nt (keys (:productions @grammar))]
                    [state nt])]
    (reduce
     (fn [ret [state nt]]
       (assoc-in ret [state nt] (slr-goto gobj state nt)))
     {} tab-cells)))

(defn slr-parser [{:keys [state-items-mappings grammar]
                   :as gobj}]
  (let [{:keys [state->items items->state]} @state-items-mappings
        productions (:productions @grammar)
        init (items->state (->> (keys items->state)
                                (filter #(contains? % lr-item))
                                first)) ;the initial state
        action (memoize (partial slr-action gobj least-attempt-resolving))
        goto (memoize (partial slr-goto gobj))]
    (letfn [(prod-len [{nt :left x :nth}]
              (count (get-in productions [nt x])))
            (default-trans [p cv]
              (conj [(:left p)] cv))]
      ;;(println "Initial state:" init ", i.e." (state->items init))
      (fn parse
        ([token-v] (parse token-v default-trans))
        ([token-v trans-fn]
         (loop [ts (seq (conj token-v {:token end-marker})) ;token queue
                ss [init] ;state stack
                treev []
                twice? false] ;parse tree stack
           ;(print ss "\t")
           (if (empty? ts) ;not suppose to happen
             (do (println ss)  treev)
             (let [t (first ts)
                   s (peek ss)
                   a (action s (:token t))]
               (case (:action a)
                 :shift
                 (do ;(println a)
                   (recur (rest ts)
                          (conj ss (:state a))
                          (conj treev t)
                          false))

                 :reduce
                 (let [p (:production a)
                       m (prod-len p)
                       nt (:left p)]
                   (recur ts
                          (let [n (count ss)
                                ss' (subvec ss 0 (- n m))
                                s' (peek ss')]
                                        ;(println nt ((nt productions) (:nth p)))
                            (conj ss' (goto s' nt)))
                          (let [n (count treev)
                                i (- n m)
                                cv (subvec treev i n)
                                treev (subvec treev 0 i)]
                            (conj treev (trans-fn p cv)))
                          false))

                 :accept
                 (do (println "accepted; tokens left:" ts "; stack:" ss)
                     (treev 0))

                 (if (not twice?)
                   (recur (conj ts {:token empty-string})
                          ss
                          treev
                          true)
                   (println "hit nil entry:" t "at" s "tree" treev)))))))))))

(tt/comprehend-tests
 (let [[only-in-expected-value
        only-in-actual-value]
       (clojure.data/diff
        {0
         {:close-paren nil,
          :times nil,
          :$ nil,
          :open-paren {:action :shift, :state 10},
          :id {:action :shift, :state 7},
          :plus nil},
         1
         {:close-paren {:action :reduce, :production {:left :e, :nth 1}},
          :times {:action :shift, :state 5},
          :$ {:action :reduce, :production {:left :e, :nth 1}},
          :open-paren nil,
          :id nil,
          :plus {:action :reduce, :production {:left :e, :nth 1}}},
         2
         {:close-paren {:action :reduce, :production {:left :f, :nth 0}},
          :times {:action :reduce, :production {:left :f, :nth 0}},
          :$ {:action :reduce, :production {:left :f, :nth 0}},
          :open-paren nil,
          :id nil,
          :plus {:action :reduce, :production {:left :f, :nth 0}}},
         3
         {:close-paren {:action :reduce, :production {:left :e, :nth 0}},
          :times {:action :shift, :state 5},
          :$ {:action :reduce, :production {:left :e, :nth 0}},
          :open-paren nil,
          :id nil,
          :plus {:action :reduce, :production {:left :e, :nth 0}}},
         4
         {:close-paren {:action :reduce, :production {:left :t, :nth 1}},
          :times {:action :reduce, :production
                  {:left :t, :nth 1}},
          :$ {:action :reduce, :production {:left :t, :nth 1}},
          :open-paren nil,
          :id nil,
          :plus {:action :reduce, :production {:left :t, :nth 1}}},
         5
         {:close-paren nil,
          :times nil,
          :$ nil,
          :open-paren {:action :shift, :state 10},
          :id {:action :shift, :state 7},
          :plus nil},
         6
         {:close-paren {:action :shift, :state 2},
          :times nil,
          :$ nil,
          :open-paren nil,
          :id nil,
          :plus {:action :shift, :state 0}},
         7
         {:close-paren {:action :reduce, :production {:left :f, :nth 1}},
          :times {:action :reduce, :production {:left :f, :nth 1}},
          :$ {:action :reduce, :production {:left :f, :nth 1}},
          :open-paren nil,
          :id nil,
          :plus {:action :reduce, :production {:left :f, :nth 1}}},
         8
         {:close-paren nil,
          :times nil,
          :$ nil,
          :open-paren {:action :shift, :state 10},
          :id {:action :shift, :state 7},
          :plus nil},
         9
         {:close-paren {:action :reduce, :production {:left :t, :nth 0}},
          :times {:action :reduce, :production {:left :t, :nth 0}},
          :$ {:action :reduce, :production {:left :t, :nth 0}},
          :open-paren nil,
          :id nil,
          :plus {:action :reduce, :production {:left :t, :nth 0}}},
         10
         {:close-paren nil,
          :times nil,
          :$ nil,
          :open-paren {:action :shift, :state 10},
          :id {:action :shift, :state 7},
          :plus nil},
         11
         {:close-paren nil,
          :times nil,
          :$ {:action :accept},
          :open-paren nil,
          :id nil,
          :plus {:action :shift, :state 0}}}
        (slr-action-tab (grammar-object test-grammar) least-attempt-resolving))]
   (t/is (and (nil? only-in-expected-value)
              (nil? only-in-actual-value)))))

(tt/comprehend-tests
 (t/is (= {0 {:e nil, :t 3, :f 4, :S nil},
           1 {:e nil, :t nil, :f nil, :S nil},
           2 {:e nil, :t nil, :f nil, :S nil},
           3 {:e nil, :t nil, :f nil, :S nil},
           4 {:e nil, :t nil, :f nil, :S nil},
           5 {:e nil, :t nil, :f 9, :S nil},
           6 {:e nil, :t nil, :f nil, :S nil},
           7 {:e nil, :t nil, :f nil, :S nil},
           8 {:e 11, :t 1, :f 4, :S nil},
           9 {:e nil, :t nil, :f nil, :S nil},
           10 {:e 6, :t 1, :f 4, :S nil},
           11 {:e nil, :t nil, :f nil, :S nil}}
          (slr-goto-tab (grammar-object test-grammar)))))

(time
 (tt/comprehend-tests
  (let [parse-fn (slr-parser (grammar-object tg/slr))
        expected-parse-tree-queens
        [:expr [{:token :let} [:decl-list [[:decl-list [[:decl-list [[:decl-list [[:decl-list [[:decl-list [[:decl-list [[:decl-list [[:decl-list [[:decl [[:var-decl [{:token :var} {:token :id, :name "N"} {:token :assign} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :digits, :value "8"}]]]]]]]]]]]]]]]]]]]]]] [:decl [[:ty-decl [{:token :type} {:token :ty-id, :name "myint"} {:token :equal} [:ty [{:token :ty-id, :name "int"}]]]]]]]] [:decl [[:ty-decl [{:token :type} {:token :ty-id, :name "intArray"} {:token :equal} [:ty [{:token :array} {:token :of} {:token :ty-id, :name "myint"}]]]]]]]] [:decl [[:var-decl [{:token :var} {:token :id, :name "row"} {:token :assign} [:expr [{:token :ty-id, :name "intArray"} {:token :open-bracket} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "N"}]]]]]]]]]]]]]]]]]] {:token :close-bracket} {:token :of} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :digits, :value "0"}]]]]]]]]]]]]]]]]]]]]]]]] [:decl [[:var-decl [{:token :var} {:token :id, :name "col"} {:token :assign} [:expr [{:token :ty-id, :name "intArray"} {:token :open-bracket} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "N"}]]]]]]]]]]]]]]]]]] {:token :close-bracket} {:token :of} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :digits, :value "0"}]]]]]]]]]]]]]]]]]]]]]]]] [:decl [[:var-decl [{:token :var} {:token :id, :name "diag1"} {:token :assign} [:expr [{:token :ty-id, :name "intArray"} {:token :open-bracket} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:cmp-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "N"}]]]]]]]] [:cal-0 [{:token :plus}]] [:term [[:factor [[:lvalue [{:token :id, :name "N"}]]]]]]]] [:cal-0 [{:token :minus}]] [:term [[:factor [{:token :digits, :value "1"}]]]]]]]]]]]]]]]] {:token :close-bracket} {:token :of} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :digits, :value "0"}]]]]]]]]]]]]]]]]]]]]]]]] [:decl [[:var-decl [{:token :var} {:token :id, :name "diag2"} {:token :assign} [:expr [{:token :ty-id, :name "intArray"} {:token :open-bracket} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:cmp-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "N"}]]]]]]]] [:cal-0 [{:token :plus}]] [:term [[:factor [[:lvalue [{:token :id, :name "N"}]]]]]]]] [:cal-0 [{:token :minus}]] [:term [[:factor [{:token :digits, :value "1"}]]]]]]]]]]]]]]]] {:token :close-bracket} {:token :of} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :digits, :value "0"}]]]]]]]]]]]]]]]]]]]]]]]] [:decl [[:fn-decl [{:token :function} {:token :id, :name "printboard"} {:token :open-paren} {:token :close-paren} {:token :equal} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :open-paren} [:expr-seq [[:expr-seq [[:expr [{:token :for} {:token :id, :name "i"} {:token :assign} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :digits, :value "0"}]]]]]]]]]]]]]]]] {:token :to} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "N"}]]]]]]]] [:cal-0 [{:token :minus}]] [:term [[:factor [{:token :digits, :value "1"}]]]]]]]]]]]]]]]] {:token :do} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :open-paren} [:expr-seq [[:expr-seq [[:expr [{:token :for} {:token :id, :name "j"} {:token :assign} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :digits, :value "0"}]]]]]]]]]]]]]]]] {:token :to} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "N"}]]]]]]]] [:cal-0 [{:token :minus}]] [:term [[:factor [{:token :digits, :value "1"}]]]]]]]]]]]]]]]] {:token :do} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :id, :name "print"} {:token :open-paren} [:expr-list [[:expr [{:token :if} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [[:lvalue [[:lvalue [{:token :id, :name "col"}]] {:token :open-bracket} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "i"}]]]]]]]]]]]]]]]]]] {:token :close-bracket}]]]]]]]] [:cmp [{:token :equal}]] [:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "j"}]]]]]]]]]]]]]]]]]] {:token :then} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [{:token :string, :value " O"}]]]]]]]]]]]] [:if-tail [{:token :else} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [{:token :string, :value " ."}]]]]]]]]]]]]]]]]]] {:token :close-paren}]]]]]]]]]]]]]]]]]]]] {:token :semi-colon} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :id, :name "print"} {:token :open-paren} [:expr-list [[:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [{:token :string, :value "\\n"}]]]]]]]]]]]]]] {:token :close-paren}]]]]]]]]]]]]]]]]]] {:token :close-paren}]]]]]]]]]]]]]]]]]]]] {:token :semi-colon} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :id, :name "print"} {:token :open-paren} [:expr-list [[:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [{:token :string, :value "\\n"}]]]]]]]]]]]]]] {:token :close-paren}]]]]]]]]]]]]]]]]]] {:token :close-paren}]]]]]]]]]]]]]]]]]]]]]] [:decl [[:fn-decl [{:token :function} {:token :id, :name "try"} {:token :open-paren} [:ty-fields [[:ty-field [{:token :id, :name "c"} {:token :colon} {:token :ty-id, :name "myint"}]]]] {:token :close-paren} {:token :equal} [:expr [{:token :if} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "c"}]]]]]]]] [:cmp [{:token :equal}]] [:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "N"}]]]]]]]]]]]]]]]]]] {:token :then} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :id, :name "printboard"} {:token :open-paren} {:token :close-paren}]]]]]]]]]]]]]]]] [:if-tail [{:token :else} [:expr [{:token :for} {:token :id, :name "r"} {:token :assign} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :digits, :value "0"}]]]]]]]]]]]]]]]] {:token :to} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "N"}]]]]]]]] [:cal-0 [{:token :minus}]] [:term [[:factor [{:token :digits, :value "1"}]]]]]]]]]]]]]]]] {:token :do} [:expr [{:token :if} [:expr [[:val [[:arith [[:or-term [[:or-term [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [[:lvalue [[:lvalue [{:token :id, :name "row"}]] {:token :open-bracket} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "r"}]]]]]]]]]]]]]]]]]] {:token :close-bracket}]]]]]]]] [:cmp [{:token :equal}]] [:cmp-term [[:term [[:factor [{:token :digits, :value "0"}]]]]]]]]]] {:token :and} [:and-term [[:cmp-term [[:term [[:factor [[:lvalue [[:lvalue [{:token :id, :name "diag1"}]] {:token :open-bracket} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "r"}]]]]]]]] [:cal-0 [{:token :plus}]] [:term [[:factor [[:lvalue [{:token :id, :name "c"}]]]]]]]]]]]]]]]]]] {:token :close-bracket}]]]]]]]] [:cmp [{:token :equal}]] [:cmp-term [[:term [[:factor [{:token :digits, :value "0"}]]]]]]]]]] {:token :and} [:and-term [[:cmp-term [[:term [[:factor [[:lvalue [[:lvalue [{:token :id, :name "diag2"}]] {:token :open-bracket} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:cmp-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "r"}]]]]]]]] [:cal-0 [{:token :plus}]] [:term [[:factor [{:token :digits, :value "7"}]]]]]] [:cal-0 [{:token :minus}]] [:term [[:factor [[:lvalue [{:token :id, :name "c"}]]]]]]]]]]]]]]]]]] {:token :close-bracket}]]]]]]]] [:cmp [{:token :equal}]] [:cmp-term [[:term [[:factor [{:token :digits, :value "0"}]]]]]]]]]]]]]]]] {:token :then} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :open-paren} [:expr-seq [[:expr-seq [[:expr-seq [[:expr-seq [[:expr-seq [[:expr-seq [[:expr-seq [[:expr-seq [[:expr [[:lvalue [[:lvalue [{:token :id, :name "row"}]] {:token :open-bracket} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "r"}]]]]]]]]]]]]]]]]]] {:token :close-bracket}]] {:token :assign} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :digits, :value "1"}]]]]]]]]]]]]]]]]]]]] {:token :semi-colon} [:expr [[:lvalue [[:lvalue [{:token :id, :name "diag1"}]] {:token :open-bracket} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "r"}]]]]]]]] [:cal-0 [{:token :plus}]] [:term [[:factor [[:lvalue [{:token :id, :name "c"}]]]]]]]]]]]]]]]]]] {:token :close-bracket}]] {:token :assign} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :digits, :value "1"}]]]]]]]]]]]]]]]]]]]] {:token :semi-colon} [:expr [[:lvalue [[:lvalue [{:token :id, :name "diag2"}]] {:token :open-bracket} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:cmp-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "r"}]]]]]]]] [:cal-0 [{:token :plus}]] [:term [[:factor [{:token :digits, :value "7"}]]]]]] [:cal-0 [{:token :minus}]] [:term [[:factor [[:lvalue [{:token :id, :name "c"}]]]]]]]]]]]]]]]]]] {:token :close-bracket}]] {:token :assign} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :digits, :value "1"}]]]]]]]]]]]]]]]]]]]] {:token :semi-colon} [:expr [[:lvalue [[:lvalue [{:token :id, :name "col"}]] {:token :open-bracket} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "c"}]]]]]]]]]]]]]]]]]] {:token :close-bracket}]] {:token :assign} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "r"}]]]]]]]]]]]]]]]]]]]]]] {:token :semi-colon} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :id, :name "try"} {:token :open-paren} [:expr-list [[:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "c"}]]]]]]]] [:cal-0 [{:token :plus}]] [:term [[:factor [{:token :digits, :value "1"}]]]]]]]]]]]]]]]]]] {:token :close-paren}]]]]]]]]]]]]]]]]]] {:token :semi-colon} [:expr [[:lvalue [[:lvalue [{:token :id, :name "row"}]] {:token :open-bracket} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "r"}]]]]]]]]]]]]]]]]]] {:token :close-bracket}]] {:token :assign} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :digits, :value "0"}]]]]]]]]]]]]]]]]]]]] {:token :semi-colon} [:expr [[:lvalue [[:lvalue [{:token :id, :name "diag1"}]] {:token :open-bracket} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "r"}]]]]]]]] [:cal-0 [{:token :plus}]] [:term [[:factor [[:lvalue [{:token :id, :name "c"}]]]]]]]]]]]]]]]]]] {:token :close-bracket}]] {:token :assign} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :digits, :value "0"}]]]]]]]]]]]]]]]]]]]] {:token :semi-colon} [:expr [[:lvalue [[:lvalue [{:token :id, :name "diag2"}]] {:token :open-bracket} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:cmp-term [[:cmp-term [[:term [[:factor [[:lvalue [{:token :id, :name "r"}]]]]]]]] [:cal-0 [{:token :plus}]] [:term [[:factor [{:token :digits, :value "7"}]]]]]] [:cal-0 [{:token :minus}]] [:term [[:factor [[:lvalue [{:token :id, :name "c"}]]]]]]]]]]]]]]]]]] {:token :close-bracket}]] {:token :assign} [:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :digits, :value "0"}]]]]]]]]]]]]]]]]]]]] {:token :close-paren}]]]]]]]]]]]]]]]] [:if-tail [{:token :ε}]]]]]]]]]]]]]]]] {:token :in} [:expr-seq [[:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :id, :name "try"} {:token :open-paren} [:expr-list [[:expr [[:val [[:arith [[:or-term [[:and-term [[:cmp-term [[:term [[:factor [{:token :digits, :value "0"}]]]]]]]]]]]]]]]]]] {:token :close-paren}]]]]]]]]]]]]]]]]]] {:token :end}]]]
    (t/is (= expected-parse-tree-queens (parse-fn (:queens tigerc.tokenizer/sample-result)))))))
