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

(defn nonterminals-not-derivable-from-start
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
             :let [nts (nonterminals-not-derivable-from-start g)]]
         (t/is (empty? nts)))
       (for [g gs'
             :let [nts (nonterminals-not-derivable-from-start g)]]
         (t/is (= non-derivable-nts nts)))))}
  [g]
  (assert (t/is (every? empty? (vals (diff-terminals-productions g))))
          (str "In the given grammar, there is 1 (or more) term(s) that"
               " neither is defined in terminals, nor has corresponding"
               " productions. The term(s) thus cannot be categorized as"
               " terminal(s) or nonterminal(s), and will render"
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
       (t/is (empty? (nonterminals-not-derivable-from-start g)))))

;;the small grammars listed above should pass grammar-inv
(tt/comprehend-tests
 (for [g [sample-cal test-grammar if-grammar]]
   (t/is (= true (grammar-inv g)))))

(defn terminal? [grammar x]
  (if (or (= x empty-string) (= x end-marker))
    true
    (contains? (:terminals grammar) x)))

(defn nonterminal? [grammar x]
  (let [ps (:productions grammar)]
    (boolean (get ps x))))

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

     (nonterminal? g x)
     ((reduce
       (fn [mem p]
         (update mem x set/union (first-set g (into p (rest xs)) mem)))
       (assoc mem x #{}) ((:productions g) x))
      x)

     :else
     (do (println "Error:" x "doesn't belong to the given grammar.")
         #{}))))

(defn- exploded-productions [{pd :productions}]
  (flatten (for [l (keys pd)]
             (for [r (pd l)]
               {:left l :right r}))))

(defn- init-follow-set [grammar]
  (let [nonterminals (keys (:productions grammar))
        start-symbol (:start grammar)]
    (-> #(assoc %1 %2 #{})
        (reduce {} nonterminals)
        (update start-symbol conj end-marker))))

(defn- init-follow-set-state [grammar]
  {:follow-set (init-follow-set grammar) :subset-rule identity})

(defn- build-follow-set-and-rules [g state {:keys [left right]}]
  (letfn [ ;;add the rule: FOLLOW(left) is a subset of FOLLOW(x)
          (chain-subset-rule [chained-rule x]
            (fn [fs]
              (let [fs' (chained-rule fs)]
                (update fs' x set/union (fs' left)))))

          (algorithm
            ([curr-state] curr-state)
            ([curr-state [x & xs]]
             (assert (nonterminal? g x))
             (if-let [x-nexts (seq (-> (first-set g xs)
                                       (disj empty-string)))]
               (update-in curr-state [:follow-set x] into x-nexts)
               (update curr-state :subset-rule chain-subset-rule x))))]
    (transduce (filter #(nonterminal? g (first %)))
               algorithm
               state (->> right (iterate rest) (take-while seq)))))

(defn- fixpoint [f x]
  (let [x' (f x)]
    (if (= x' x) ;powerful '='!
      x'
      (recur f x'))))

(defn follow-set
  {:test
   #(let [empty-g {:terminals #{empty-string}
                   :start :e
                   :productions {:e [[empty-string]]}}
          left-recursive-g (update-in empty-g [:productions :e]
                                      conj [:e])
          simple-g (-> empty-g
                       (update :terminals conj \.)
                       (update-in [:productions :e] conj [:e \.]))
          require-converge-g (-> empty-g
                                 (update :terminals set/union #{\, \.})
                                 (update-in [:productions :e] conj [:e \, :t])
                                 (assoc-in [:productions :t] [[:t \.]]))]
      (tt/comprehend-tests
       (let [flwset (follow-set empty-g)]
         (t/is (= #{end-marker} (:e flwset))))
       (let [flwset (follow-set left-recursive-g)]
         (t/is (= #{end-marker} (:e flwset))))
       (let [flwset (follow-set simple-g)]
         (t/is (= #{end-marker \.} (:e flwset))))
       (let [flwset (follow-set require-converge-g)]
         [(t/is (= #{end-marker \,} (:e flwset)))
          (t/is (= #{end-marker \, \.} (:t flwset)))])
       (let [flwset (follow-set tg/slr)
             lvalue #{end-marker :slash :close-paren :semi-colon :do :else
                      :close-bracket :pipe :comma :type :geq :minus
                      :open-bracket :star :function :assign :var :diamond
                      :gt :plus :then :and :close-brace :period :equal :end
                      :leq :lt :in :to}]
         [(t/is (empty? (set/difference (:lvalue flwset) lvalue)))
          (t/is (empty? (set/difference lvalue (:lvalue flwset))))])))}
  [g]
  (let [init-state (init-follow-set-state g)
        converge-state #(fixpoint (:subset-rule %) (:follow-set %))]
    (converge-state
     (reduce (partial build-follow-set-and-rules g)
             init-state (exploded-productions g)))))

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

(defn valid-lr-item? [g item-x]
  (let [{nt :left x :nth y :pos} item-x
        prod-dict (:productions g)
        v (nt prod-dict)]
    (and v (>= x 0) (>= y 0) (< x (count v)) (<= y (count (v x))))))

;;expect valid item
(defn end-lr-item?
  "Is the item at the end of its production?"
  [g item-x]
  (let [{nt :left x :nth y :pos} item-x
        prod-dict (:productions g)
        n (count ((nt prod-dict) x))]
    (= n y)))

;;expect valid item
(defn decode-lr-item [g item-x]
  (let [{nt :left x :nth y :pos} item-x
        prod-dict (:productions g)]
    (((nt prod-dict) x) y)))

;;expect valid item
(defn forward-lr-item [g item-x]
  (let [{nt :left x :nth y :pos} item-x
        prod-dict (:productions g)
        limit (count ((nt prod-dict) x))
        y (inc y)]
    (if (<= y limit) (assoc item-x :pos y))))

(defn lr-closure
  {:test
   #(let [{pd :productions :as g}
          test-grammar

          start-item
          {:left (:start g) :nth 0 :pos 0}

          items-at-terminal
          (->> item
               (for [i (range (count ((pd l) n)))
                     :let [item {:left l :nth n :pos i}
                           decoded (decode-lr-item g item)]
                     :when (terminal? g decoded)])
               (for [n (range (count (pd l)))])
               (for [l (keys pd)])
               flatten)

          step-item
          {:left :t :nth 0 :pos 2}]
      (tt/comprehend-tests
       (t/is (= #{} (lr-closure #{} g)))
       (for [item items-at-terminal]
         (t/is (= #{item} (lr-closure #{item} g))))
       (t/is (= #{step-item
                  {:left :f :nth 0 :pos 0}
                  {:left :f :nth 1 :pos 0}}
                (lr-closure #{step-item} g)))
       (t/is (= #{start-item
                  {:left :e, :nth 1, :pos 0}
                  {:left :t, :nth 0, :pos 0}
                  {:left :t, :nth 1, :pos 0}
                  {:left :f, :nth 0, :pos 0}
                  {:left :f, :nth 1, :pos 0}}
                (lr-closure #{start-item} g)))))}
  [lr-item-set {pd :productions :as g}]
  (assert (every? (partial valid-lr-item? g) lr-item-set))
  (let [decode
        (partial decode-lr-item g)

        nonterminal-item?
        (comp (partial nonterminal? g) decode)

        nonterminal-items
        (partial set/select nonterminal-item?)

        items-at-the-beginning
        (fn [nt]
          (->> {:left nt :nth n :pos 0}
               (for [n (range (count (pd nt)))])))

        expand-per-nt-item
        (fn [ret nt-item]
          (into ret (items-at-the-beginning (decode nt-item))))

        expand
        (fn [r]
          (reduce expand-per-nt-item r (nonterminal-items r)))]
    (fixpoint expand lr-item-set)))

(defn lr-goto [lr-item-set x g]
  (assert (and (or (terminal? g x) (nonterminal? g x))
               (every? (partial valid-lr-item? g) lr-item-set)))
  (let [lr-item-set (loop [r #{} s (seq lr-item-set)]
                      (if (empty? s) r
                          (recur
                           (let [item-y (first s)]
                             (if (end-lr-item? g item-y) r
                                 (let [y (decode-lr-item g item-y)]
                                   (if (not (= y x)) r
                                     (conj r (forward-lr-item g item-y))))))
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
        decode     (partial decode-lr-item g)
        end?       (partial end-lr-item? g)
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

