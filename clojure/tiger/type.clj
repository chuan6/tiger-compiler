(ns type)

;;;Implements the disjoint-set forest data structure.

;;;A valid one would include one or many sets, each represented by a tree.
;;;Each tree organizes a number of type names; no two trees share type names,
;;;and any two type names within the same tree are equivalent.

;;;At each snapshot of the data structure, root of each tree should have a
;;;reference to an entity of type expression, be it int, string, record, or
;;;array. A tree whose root doesn't have such a reference is invalid,
;;;indicating an appearance of alias definition cycle.

(def kind-set
  #{:void :int :string :nil :record :array :alias})

(defn init
  "initialize an empty type"
  [] (ref {:rank 0 :path ()}))

(defn type? [x]
  (and (instance? clojure.lang.Ref x)
       (let [v @x] (contains? v :rank) (contains? v :path))))

(defn expr
  "create a type entity according to the given type expression"
  [env ty-expr]
  (let [[label body] ty-expr]
    (case label
      :alias
      (condp = body
        'int {:kind :int}
        'string {:kind :string}
        nil)

      :array
      {:kind :array
       :elem-type (let [tid body
                        type (get (:ty-id env) tid)]
                    (assert type
                            "array element expect existing type")
                    type)}

      :record
      {:kind :record
       :fieldv (loop [fs (seq body) fv [] s #{}]
                 (if (empty? fs)
                   fv
                   (let [[name tid] (first fs)
                         type (get (:ty-id env) tid)]
                     (assert type "field expect existing type")
                     (assert (not (contains? s name))
                             "duplicate field name found")
                     (recur (rest fs)
                            (conj fv {:name name :type type})
                            (conj s name)))))})))

(declare find-set)

(defn get-entity
  "get the type entity associated with the given type"
  [x] (if-let [e (:entity @x)]
        ;;if e is not nil, it should be the same as the
        ;;entity attached to the root
        e (:entity (deref (find-set x)))))

(defn attach-entity
  "attach a type entity created by expr to a type"
  [x entity]
  (assert (nil? (get-entity x)) "type entity conflict")
  (dosync (alter x assoc :entity entity)))

(defn entity-attached?
  "determine if there is an entity attached to the given type"
  [x] (not (nil? (get-entity x))))

(declare link)

(defn let-equal
  "establish equivalence between the two given types"
  [x y]
  (let [xr (find-set x) yr (find-set y)]
    (if (= xr yr)
      (:entity @xr)
      (let [ex (:entity @xr) ey (:entity @yr)
            ex-nil? (nil? ex) ey-nil? (nil? ey)]
        (assert (or ex-nil? ey-nil?) "type entity conflict")
        (cond (and ex-nil? ey-nil?) ;no entity is attached to either
              (link xr yr)

              ex-nil? ;an entity is attached to yr
              (-> (link xr yr) (attach-entity ey))

              ey-nil? ;an entity is attached to xr
              (-> (link xr yr) (attach-entity ex)))))))

(defn equal?
  "determine equivalence of the two given types"
  [x y]
  (let [xr (find-set x) yr (find-set y)]
    (if (= xr yr)
      true
      (let [kx (:kind (:entity @xr))
            ky (:kind (:entity @yr))]
        (case [kx ky]
          [:int :int] true
          [:string :string] true
          [:nil :record] true
          [:record :nil] true
          [:nil :array] true
          [:array :nil] true
          false)))))

(defn reflect [x kind]
  (= (:kind (get-entity x)) kind))

(defn void? [x] (reflect x :void))

(defn string? [x] (reflect x :string))

(defn int? [x] (reflect x :int))

(defn record? [x] (reflect x :record))

(defn link [x y]
  "link by rank"
  (let [{r :rank p :path} @x
        {s :rank q :path} @y]
    (if (< r s)
      (dosync (alter x assoc :path (conj q y))
              y)
      (dosync (alter y assoc :path (conj p x))
              (if (= r s) (alter x assoc :rank (inc r)))
              x))))

(defn find-set
  "find set and do path compression along the way"
  [x]
  (if-let [p (first (:path @x))]
    (dosync (let [r (find-set p)]
              (alter x assoc :path `(~r))
              r))
    x))

(defn cons-int []
  (let [t (init) e {:kind :int}]
    (do (attach-entity t e) t)))

(defn cons-string []
  (let [t (init) e {:kind :string}]
    (do (attach-entity t e) t)))

(def nil-expr (ref {:rank 0 :path () :entity {:kind :nil}}))



