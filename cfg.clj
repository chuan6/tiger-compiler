(ns cfg
  (:require [clojure.set :as set]
            [clojure.test :as t]
            [grammar :as tg]
            [tigerc.test :as tt]))

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

(def test-grammar ;from the Dragon book
  {:terminals #{:plus :times :open-paren :close-paren :id}
   :start :e
   :productions
   {:e [[:e :plus :t] [:t]]
    :t [[:t :times :f] [:f]]
    :f [[:open-paren :e :close-paren] [:id]]}})

(def if-grammar
  {:terminals #{:if :then :else}
   :start :e
   :productions
   {:e [[:if :e :then :e] [:if :e :then :e :else :e]]}})

(defn diff-terminals-productions
  {:test
   #(let [empty-g {:terminals #{} :productions {}}
          gs [{:terminals #{:digit}
               :start :e
               :productions {:e [[:e :digit] [:digit]]}}
              sample-cal test-grammar if-grammar]
          terms #{:extra-terminal}
          gs-more-terms (map (fn [g]
                               (update g :terminals
                                       clojure.set/union terms))
                             gs)
          gs-missed-term (map (fn [g]
                                (let [t (first (:terminals g))]
                                  [(update g :terminals disj t) t]))
                              gs)]
      (tt/comprehend-tests
       (let [{:keys [only-in-terminals only-in-productions]}
             (diff-terminals-productions empty-g)]
         [(t/is (empty? only-in-terminals))
          (t/is (empty? only-in-productions))])
       (for [g gs
             :let [{:keys [only-in-terminals only-in-productions]}
                   (diff-terminals-productions g)]]
         [(t/is (empty? only-in-terminals))
          (t/is (empty? only-in-productions))])
       (for [g gs-more-terms
             :let [{:keys [only-in-terminals only-in-productions]}
                   (diff-terminals-productions g)]]
         [(t/is (= terms only-in-terminals))
          (t/is (empty? only-in-productions))])
       (for [[g t] gs-missed-term
             :let [{:keys  [only-in-terminals only-in-productions]}
                   (diff-terminals-productions g)]]
         [(t/is (empty? only-in-terminals))
          (t/is (= #{t} only-in-productions))])))}
  [g]
  (let [target (:terminals g)
        prod-dict (:productions g)
        tset (clojure.set/difference (set (flatten (vals prod-dict)))
                                     (set (keys prod-dict)))]
    {:only-in-terminals (clojure.set/difference target tset)
     :only-in-productions (clojure.set/difference tset target)}))

(defn non-terminals-not-derivable-from-start
  {:test
   #(let [gs [{:terminals #{:digit}
               :start :e
               :productions {:e [[:e :digit] [:digit]]}}
              sample-cal test-grammar if-grammar]
          extra-term empty-string
          extra-nterm-prod {:extra-nonterminal [[extra-term]]}
          gs' (map (fn [g] (-> g
                               (update :productions into extra-nterm-prod)
                               (update :terminals conj extra-term)))
                   gs)
          non-derivable-nts (set (keys extra-nterm-prod))]
      (tt/comprehend-tests
       (for [g gs
             :let [nts (non-terminals-not-derivable-from-start g)]]
         (t/is (empty? nts)))
       (for [g gs'
             :let [nts (non-terminals-not-derivable-from-start g)]]
         (t/is (= non-derivable-nts nts)))))}
  [g]
  (assert (t/is (every? empty? (vals (diff-terminals-productions g))))
          (str "In the given grammar, there is 1 (or more) term(s) that"
               " neither is defined in terminals, nor has corresponding"
               " productions. The term(s) thus cannot be categorized as"
               " terminal(s) or non-terminal(s), and will render"
               " this function ineffective."))
  (let [nts (set (keys (:productions g)))]
   (loop [nts-processed #{}
          nts-to-be-reached #{(:start g)}]
     (if (empty? nts-to-be-reached)
       (clojure.set/difference nts nts-processed)
       (let [nts-processed' (into nts-processed nts-to-be-reached)]
        (recur nts-processed'
               (set (->> nts-to-be-reached
                         (select-keys (:productions g))
                         vals
                         flatten
                         (remove (:terminals g))
                         (remove nts-processed')))))))))

(defn- grammar-inv [g]
  (and (t/is (every? empty? (vals (diff-terminals-productions g))))
       (t/is (empty? (non-terminals-not-derivable-from-start g)))))

;;the small grammars listed above should pass grammar-inv
(tt/comprehend-tests
 (for [g [sample-cal test-grammar if-grammar]]
   (t/is (= true (grammar-inv g)))))

(defn terminal? [grammar x]
  (if (or (= x empty-string) (= x end-marker))
    true
    (contains? (:terminals grammar) x)))

(defn non-terminal? [grammar x]
  (let [ps (:productions grammar)]
    (not (nil? (get ps x)))))

(defn first-set
  {:test
   #(let [g tg/slr
          single-term-inputs (for [t (:terminals g)] [t])
          two-terms-inputs (for [t (:terminals g) s (:terminals g)] [s t])
          start-symbol-input [(:start g)]
          empty-string-input [:if-tail :lvalue]
          undefined-token-input [:if-tail :undefined-token]]
      (tt/comprehend-tests
       (for [xs single-term-inputs]
         (t/is (= #{(first xs)} (first-set g xs))))
       (for [xs two-terms-inputs
             :let [x (first xs)]
             :when (not= x empty-string)]
         (t/is (= #{x} (first-set g xs))))
       (for [xs two-terms-inputs
             :let [x (first xs)]
             :when (= x empty-string)]
         (t/is (= (set xs) (first-set g xs))))
       (t/is (= #{:ty-id :let :if :digits :minus :string :open-paren
                  :break :for :id :nil :while}
                (first-set g start-symbol-input)))
       (t/is (= #{:else empty-string :id}
                (first-set g empty-string-input)))
       (t/is (= #{:else empty-string}
                (first-set g undefined-token-input)))))}
  ([g xs] (first-set g xs {}))
  ([g [x :as xs] mem]
   (cond
     (empty? xs)
     #{}

     (= x empty-string)
     (conj (first-set g (rest xs) mem) empty-string)

     (terminal? g x)
     #{x}

     (contains? mem x)
     (mem x)

     (non-terminal? g x)
     ((reduce
       (fn [mem p]
         (update mem x set/union (first-set g (into p (rest xs)) mem)))
       (assoc mem x #{}) ((:productions g) x))
      x)

     :else
     (do (println "Error:" x "doesn't belong to the given grammar.")
         #{}))))

;(def init-follow-set
 ; {:expr #{} :expr-helper #{}
  ; :term #{} :term-helper #{}
   ;:factor #{}})

(defn- init-follow-set [grammar]
  (let [nonterminals (keys (:productions grammar))
        start-symbol (:start grammar)]
    (-> #(assoc %1 %2 #{})
        (reduce {} nonterminals)
        (update start-symbol conj end-marker))))

(defn- init-follow-set-state [grammar]
  {:follow-set (init-follow-set grammar) :subset-rule identity})

(defn- fixpoint [f x]
  (let [x' (f x)]
    (if (= x' x) ;powerful '='!
      x'
      (recur f x'))))

(defn follow-set-production [grammar left right state]
  (let [chain-subset-rule ;add the rule: FOLLOW(left) is a subset of FOLLOW(x)
        (fn [chained-rule x]
          (fn [fs] (let [fs' (chained-rule fs)]
                     (update fs' x set/union (fs' left)))))]
    (loop [right right
           state state]
      (if (empty? right)
        state
        (let [x (first right)
              xs (rest right)]
          (cond
            (terminal? grammar x) (recur xs state)
            (non-terminal? grammar x)
            (let [x-next (first-set grammar (vec xs))
                  state' (update-in state [:follow-set x]
                                    set/union (disj x-next empty-string))]
              (if (or (empty? x-next) (contains? x-next empty-string))
                ;; add rule "FOLLOW(left) is a subset of FOLLOW(x)"
                ;; to (:subset-rule state). ff chains all the rules found,
                ;; and will produce a final rule which is to be
                ;; applied to fixpoint function.
                (recur xs (update state' :subset-rule chain-subset-rule x))
                (recur xs state')))
            ;;TODO :else
            ))))))

(defn follow-set [grammar]
  (let [prods (seq (:productions grammar))]
    (loop [prods prods
           state (init-follow-set-state grammar)]
      (if (empty? prods)
        (fixpoint (:subset-rule state) (:follow-set state))
        (recur (rest prods)
               (let [prod (first prods)
                     left (nth prod 0)]
                 (loop [alts (nth prod 1)
                        state state]
                   (if (empty? alts)
                     state
                     (let [right (first alts)]
                       (if (= right empty-string)
                         (recur (rest alts) state)
                         (recur (rest alts)
                                (follow-set-production grammar left right state))))))))))))

(t/is
 (= (follow-set tg/slr)
    {:ty-field #{:close-paren :comma :close-brace}
     :or-term #{:close-paren :semi-colon :do :else :close-bracket :pipe
                :comma :type :$ :function :var :then :and :close-brace
                :end :in :to}
     :expr-seq #{:close-paren :semi-colon :end}
     :if-tail #{:close-paren :semi-colon :do :else :close-bracket :comma
                :type :$ :function :var :then :close-brace :end :in :to}
     :var-decl #{:type :function :var :in}
     :decl-list #{:type :function :var :in}
     :cmp #{:digits :string :open-paren :id :nil}
     :expr-list #{:close-paren :comma}
     :ty #{:type :function :var :in}
     :arith #{:close-paren :semi-colon :do :else :close-bracket :pipe
              :comma :type :$ :function :var :then :close-brace :end
              :in :to}
     :cal-1 #{:digits :open-paren :id :nil}
     :val #{:close-paren :semi-colon :do :else :close-bracket :comma :type
            :$ :function :var :then :close-brace :end :in :to}
     :lvalue #{:slash :close-paren :semi-colon :do :else :close-bracket
               :pipe :comma :type :geq :minus :open-bracket :star :$
               :function :assign :var :diamond :gt :plus :then :and
               :close-brace :period :equal :end :leq :lt :in :to}
     :term #{:slash :close-paren :semi-colon :do :else :close-bracket :pipe
             :comma :type :geq :minus :star :$ :function :var :diamond :gt
             :plus :then :and :close-brace :equal :end :leq :lt :in :to}
     :cmp-term #{:close-paren :semi-colon :do :else :close-bracket :pipe
                 :comma :type :geq :minus :$ :function :var :diamond :gt
                 :plus :then :and :close-brace :equal :end :leq :lt :in
                 :to}
     :ty-fields #{:close-paren :comma :close-brace}
     :field-list #{:comma :close-brace}
     :ty-decl #{:type :function :var :in}
     :cal-0 #{:digits :open-paren :id :nil}
     :decl #{:type :function :var :in}
     :expr #{:close-paren :semi-colon :do :else :close-bracket :comma :type
             :$ :function :var :then :close-brace :end :in :to}
     :factor #{:slash :close-paren :semi-colon :do :else :close-bracket
               :pipe :comma :type :geq :minus :star :$ :function :var
               :diamond :gt :plus :then :and :close-brace :equal :end :leq
               :lt :in :to}
     :fn-decl #{:type :function :var :in},
     :and-term #{:close-paren :semi-colon :do :else :close-bracket :pipe
                 :comma :type :$ :function :var :then :and :close-brace
                 :end :in :to}}))

(def aug-start :S)
(defn aug-start-inv [g] (and (nil? (aug-start (:productions g)))
                             (nil? ((:terminals g) aug-start))))

(defn augment-grammar [g]
  (assert (grammar-inv g))
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

;;expect augmented grammar
(defn canonical-coll [g]
  (let [symbols (list-grammar-symbols g)

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
    (fixpoint f coll)))

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

;;expect augmented grammar
(defn slr-action-tab [g ccc prefer-shift?]
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
          ;;note: continue reduction after an action has been found,
          ;;in order to check existence of any action conflictions
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
                  act'
                  (let [a0 (:action act) a1 (:action act')]
                    (if (and (not (= a0 a1)) prefer-shift?)
                      (condp = :shift
                        a0 act
                        a1 act')
                      (reduced (println "Inconsistency:" act' "with" act
                                        "at" "[" (state its) "," a  "]")))))
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

;;expect augmented grammar
(defn slr-goto-tab [g ccc]
  (let [nterms (keys (:productions g))
        state  (fn [items] (state-by-items ccc items))
        goto   (fn [its s] (lr-goto its s g))

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

(defn slr-parser [g]
  (let [g   (augment-grammar g)
        ccc (consolidate-cc (canonical-coll g))

        init ;the initial state
        (let [it {:left aug-start :nth 0 :pos 0}
              v (:by-x ccc) n (count v)]
          (loop [i 0]
            (if (= i n)
              (println "cannot find initial state from canonical collection")
              (if (contains? (v i) it)
                i (recur (inc i))))))

        action-tab (slr-action-tab g ccc false)
        goto-tab (slr-goto-tab g ccc)

        atab-helper
        (fn [state term f]
          (let [r (get (action-tab state) term)]
            (if r r
                ;;otherwise, try consuming an empty-string
                (let [s (get (action-tab state) empty-string)]
                  (if s (f (:state s) term f))))))
        atab ;get an entry from action table
        (fn [state term] (atab-helper state term atab-helper))
        
        gtab ;get an entry from goto table
        (fn [state nterm] (get (goto-tab state) nterm))

        prod-len ;count non-empty-string symbols in a production
        (fn [prod]
          (let [pv (((:left prod) (:productions g)) (:nth prod))
                n (count pv)]
            (loop [c 0 i 0]
              (if (= i n)
                c
                (recur (if (= (pv i) empty-string) c (inc c))
                       (inc i))))))

        default-trans
        (fn [p cv] (conj [(:left p)] cv))
        ]
    (println "Initial state:" init ", i.e." (items-by-state ccc init))
    (fn parse
      ([token-v] (parse token-v default-trans))
      ([token-v trans-fn]
       (loop [ts (seq (conj token-v {:token end-marker})) ;token queue
              ss [init] ;state stack
              treev []] ;parse tree stack
         (print ss "\t")
         (if (empty? ts) ;not suppose to happen
           (do (println ss)  treev)
           (let [t (first ts) s (peek ss)
                 a (atab s (:token t))]
             (case (:action a)
               :shift
               (do (println a)
                   (recur (rest ts) (conj ss (:state a))
                          (conj treev t)))

               :reduce
               (let [p (:production a)
                     m (prod-len p)
                     nt (:left p)]
                 (recur ts
                        (let [n (count ss)
                              ss (subvec ss 0 (- n m))]
                          (println nt ((nt (:productions g)) (:nth p)))
                          (conj ss (gtab (peek ss) nt)))
                        (let [n (count treev)
                              i (- n m)
                              cv (subvec treev i n)
                              treev (subvec treev 0 i)]
                          (conj treev (trans-fn p cv)))))

               :accept
               (do (println "accepted; tokens left:" ts "; stack:" ss)
                   (treev 0))

               (println "hit nil entry:" t "at" s "tree" treev)))))))))

