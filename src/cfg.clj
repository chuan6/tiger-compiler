(ns cfg
  (:require [clojure.data]
            [clojure.set :as set]
            [clojure.test :as t]
            [tigerc.grammar :as tg]
            [tigerc.test :as tt]))

(def empty-string :ε)
(def end-marker :$)

(def empty-grammar
  {:terminals #{empty-string}
   :start :e
   :productions {:e [[empty-string]]}})

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

(def ^:private sample-grammars
  [empty-grammar sample-cal test-grammar if-grammar])

(defn list-grammar-symbols
  {:test
   #(tt/comprehend-tests
     (t/is (= #{:e empty-string} (list-grammar-symbols empty-grammar)))
     (t/is (= #{:plus :times :open-paren :close-paren :id :e :t :f}
              (set (list-grammar-symbols test-grammar)))))}
  [{ts :terminals pd :productions}]
  (into ts (keys pd)))

(defn diff-terminals-productions
  {:test
   #(let [gs (into [{:terminals #{:digit}
                     :start :e
                     :productions {:e [[:e :digit] [:digit]]}}]
                   sample-grammars)
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
             (diff-terminals-productions empty-grammar)]
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
   #(let [gs (into [{:terminals #{:digit}
                     :start :e
                     :productions {:e [[:e :digit] [:digit]]}}]
                   sample-grammars)
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
 (for [g sample-grammars]
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
             (if-let [x-nexts (seq (first-set g xs))]
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
   #(let [g empty-grammar
          left-recursive-g (update-in g [:productions :e] conj [:e])
          simple-g (-> g
                       (update :terminals conj \.)
                       (update-in [:productions :e] conj [:e \.]))
          require-converge-g (-> g
                                 (update :terminals set/union #{\, \.})
                                 (update-in [:productions :e] conj [:e \, :t])
                                 (assoc-in [:productions :t] [[:t \.]]))]
      (tt/comprehend-tests
       (let [flwset (follow-set g)]
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
                      :leq :lt :in :to empty-string}]
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

(declare end-position-lr-item?)
(declare decode-lr-item)

(defn valid-lr-item?
  {:test
   #(let [{pd :productions :as g} test-grammar
          all-valid-items (->> {:left nt :nth x :pos y}
                           (for [y (range (inc (count ((pd nt) x))))])
                           (for [x (range (count (pd nt)))])
                           (for [nt (keys pd)])
                           flatten)
          invalid-items [{:left :not-defined :nth 0 :pos 0}
                         {:left :e :nth 0 :pos -1}
                         {:left :e :nth 0 :pos 4}
                         {:left :e :nth -1 :pos 0}
                         {:left :e :nth 2 :pos 0}]]
      (tt/comprehend-tests
       (for [item all-valid-items]
         (t/is (valid-lr-item? g item)))
       (for [item invalid-items]
         (t/is (not (valid-lr-item? g item))))))}
  [g item]
  (or (end-position-lr-item? g item)
      (boolean (decode-lr-item g item))))

;;expect valid item
(defn end-position-lr-item?
  "Is the item at the end of its production?"
  {:test
   #(let [{pd :productions :as g} test-grammar

          items-at-the-end-position
          (->> {:left nt :nth x :pos (count ((pd nt) x))}
               (for [x (range (count (pd nt)))])
               (for [nt (keys pd)])
               flatten)

          items-not-at-the-end-position
          (into [{:left :not-defined :nth 0 :pos 0}
                 {:left :e :nth 0 :pos 4}
                 {:left :e :nth 0 :pos 2}]
                (->> {:left nt :nth x :pos 0}
                     (for [x (range (count (pd nt)))])
                     (for [nt (keys pd)])
                     flatten))]
      (tt/comprehend-tests
       (for [item items-at-the-end-position]
         (t/is (end-position-lr-item? g item)))
       (for [item items-not-at-the-end-position]
         (t/is (not (end-position-lr-item? g item))))))}
  [{pd :productions} {nt :left x :nth y :pos}]
  (when-let [prod-alt (get-in pd [nt x])]
    (= (count prod-alt) y)))

;;expect valid item
(defn decode-lr-item
  {:test
   #(let [g test-grammar]
      (tt/comprehend-tests
       (t/is (= :e (decode-lr-item g {:left :e :nth 0 :pos 0})))
       (t/is (= :t (decode-lr-item g {:left :e :nth 0 :pos 2})))
       (t/is (nil? (decode-lr-item g {:left :not-defined :nth 0 :pos 0})))
       (t/is (nil? (decode-lr-item g {:left :e :nth 0 :pos 3})))))}
  [{pd :productions} {nt :left x :nth y :pos}]
  (get-in pd [nt x y]))

;;expect valid item
(defn forward-lr-item
  {:test
   #(let [g test-grammar]
      (tt/comprehend-tests
       (t/is (= {:left :e :nth 0 :pos 1} (forward-lr-item g {:left :e :nth 0 :pos 0})))
       (t/is (= {:left :e :nth 0 :pos 2} (forward-lr-item g {:left :e :nth 0 :pos 1})))
       (t/is (= {:left :e :nth 0 :pos 3} (forward-lr-item g {:left :e :nth 0 :pos 2})))
       (t/is (nil? (forward-lr-item g {:left :e :nth 0 :pos 3})))))}
  [g item]
  (when-not (end-position-lr-item? g item)
    (update item :pos inc)))

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
  [lr-itemset {pd :productions :as g}]
  (assert (every? (partial valid-lr-item? g) lr-itemset)
          (str "failed item set: " lr-itemset " and g: " g))
  (let [decode
        (partial decode-lr-item g)

        nonterminal-item?
        (comp (partial nonterminal? g) decode)

        nonterminal-items
        (partial set/select nonterminal-item?)

        items-at-the-beginning
        (memoize
         (fn [nt]
           (->> {:left nt :nth n :pos 0}
                (for [n (range (count (pd nt)))]))))

        expand-per-nt-item
        (fn [ret nt-item]
          (into ret (items-at-the-beginning (decode nt-item))))

        expand
        (fn [r]
          (reduce expand-per-nt-item r (nonterminal-items r)))]
    (fixpoint expand lr-itemset)))

(defn lr-goto
  {:test
   #(let [{pd :productions :as g}
          test-grammar

          items-at-the-end-position
          (->> {:left nt :nth x :pos (count ((pd nt) x))}
               (for [x (range (count (pd nt)))])
               (for [nt (keys pd)])
               flatten)

          items-not-at-the-end-position
          (->> {:left nt :nth x :pos y}
               (for [y (range (count ((pd nt) x)))])
               (for [x (range (count (pd nt)))])
               (for [nt (keys pd)])
               flatten)]
      (tt/comprehend-tests
       (t/is (= #{} (lr-goto #{} :e g)))
       (for [item items-not-at-the-end-position
             :let [sym (decode-lr-item g item)
                   ret (lr-goto #{item} sym g)]]
         [(t/is (= (lr-closure ret g) ret))
          (t/is (= (lr-closure #{(forward-lr-item g item)} g) ret))])
       (for [item items-at-the-end-position]
         (for [sym (list-grammar-symbols g)
               :let [ret (lr-goto g #{item} sym)]]
           [(t/is (= (lr-closure ret g) ret))
            (t/is (= #{} ret))]))
       (t/is (= #{{:left :e, :nth 0, :pos 1}
                  {:left :f, :nth 0, :pos 2}}
                (lr-goto g #{{:left :e :nth 0 :pos 0}
                             {:left :f :nth 0 :pos 1}} :e)))))}
  [g lr-itemset x]
  (assert (or (terminal? g x) (nonterminal? g x)))
  (assert (every? (partial valid-lr-item? g) lr-itemset))
  (let [new-kernel-items
        (->> lr-itemset
             (filter #(= (decode-lr-item g %) x))
             (map (partial forward-lr-item g)))]
    (lr-closure (set new-kernel-items) g)))

(defn- symbols-in-lr-itemset [g state]
  (->> (map (partial decode-lr-item g) state)
       (remove nil?)))

;;expect augmented grammar
(defn canonical-coll
  {:test
   #(let [gs (map augment-grammar sample-grammars)

          valid-result?
          (fn [g coll]
            (->> (contains? coll (lr-goto g state sym))
                 (for [sym (symbols-in-lr-itemset g state)])
                 (for [state coll])))]
      (tt/comprehend-tests
       (for [g gs]
         (t/is (valid-result? g (canonical-coll g))))))}
  [g]
  (letfn [(generate-states [coll]
            (->> (lr-goto g state sym)
                 (for [sym (symbols-in-lr-itemset g state)])
                 (for [state coll])
                 flatten))

          (update-coll [coll]
            (into coll (filter seq (generate-states coll))))]
    (fixpoint update-coll #{(lr-closure #{lr-item} g)})))

(defn indexed-canonical-coll
  "produce two mappings: state->items and items->state, that are consistent,
  meaning,
  1) given a valid itemset x, we have (= x (state->items (items->state x)));
  2) given a valid state i, we have (= i (items->state (state->items i)))"
  {:test
   #(let [gs (map augment-grammar sample-grammars)]
      (tt/comprehend-tests
       (for [g gs
             :let [cc
                   (canonical-coll g)

                   {:keys [state->items items->state]}
                   (indexed-canonical-coll cc)]]
         [(t/is (= cc (set (vals state->items))))
          (t/is (= (set/map-invert state->items) items->state))])))}
  [cc]
  (let [cc-seq (seq cc)
        swap-pair (fn [x y] [y x])]
    {:state->items (into {} (map-indexed vector cc-seq))
     :items->state (into {} (map-indexed swap-pair cc-seq))}))
