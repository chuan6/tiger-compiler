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

(declare equal?)

;;built-in types: int, string, nil, void(or 'no-value')
(def int (init))
(def string (init))
(def nil-expr (init))
(def void (init))

(defn int? [x] (equal? x int)) ;int may be aliased, thus use equal?
(defn string? [x] (equal? x string)) ;same as int?
(defn nil-expr? [x] (= x nil-expr)) ;nil-expr isn't to be aliased
(defn void? [x] (= x void)) ;same as nil-expr?

(defn built-in? [x] (or (int? x) (string? x) (nil-expr? x) (void? x)))

(defn- find-set
  "find the representative and do path compression along the way"
  [x]
  (if-let [p (first (:path @x))]
    ;;do path compression along the path
    (dosync (let [r (find-set p)]
              (alter x assoc :path `(~r))
              r))
    ;;or, x is itself a representative
    x))

(defn equal?
  "handle type equivalence that is complicated by type aliasing"
  [x y]
  (if (= x y)
    true
    (let [rx (find-set x) ry (find-set y)]
      (if (= rx ry)
        true
        (or ;one is nil, and the other is a record or an array
         (and (nil-expr? rx) (not (nil? (:struct @ry))))
         (and (nil-expr? ry) (not (nil? (:struct @rx)))))))))

(defn attach-struct
  "attach to representative a type structure (array or record)"
  [x struct]
  (let [rx (find-set x)]
    (assert (or (built-in? rx) (nil? (:struct @rx)))
            "type structure conflict")
    (dosync (alter rx assoc :struct
                   ;;make it lazy to support recursive data
                   (fn [] (delay struct)))
            ;;return nil as a procedure
            nil)))

(defn struct-attached? [x]
  (let [rx (find-set x)]
    (not (nil? (:struct @rx)))))

(defn- link [x y]
  "link by rank"
  (let [{r :rank p :path} @x
        {s :rank q :path} @y]
    (if (< r s)
      (dosync (alter x assoc :path (conj q y))
              y)
      (dosync (alter y assoc :path (conj p x))
              (if (= r s) (alter x assoc :rank (inc r)))
              x))))

(defn let-equal
  "establish equivalence between the two given types; return nil"
  [x y]
  (let [rx (find-set x) ry (find-set y)]
    (if (= rx ry)
      nil
      (let [sx (:struct @rx) sy (:struct @ry)
            sx-nil? (nil? sx) sy-nil? (nil? sy)]
        (assert (not (or sx-nil? sy-nil?)) "type entity conflict")
        (cond (and sx-nil? sy-nil?) ;no structure is attached to either
              (link rx ry)

              sx-nil? ;sy is the structure
              (-> (link rx ry) (attach-struct sy))

              sy-nil? ;sx is the structure
              (-> (link rx ry) (attach-struct sx)))))))

(comment record?
         "used at semantics/do-lvalue: ensure that field access is
only available on value of record type."
         "used at semantics/do-record: ensure that the given type
name refers to a record type.")

(comment array?
         "used at semantics/do-array: ensure that the given type
name refers to an array type."
         "used at semantics/do-lvalue: ensure that index access is
only available on value of array type.")

(comment expr
         "used at semantics/do-consec-ty-decl: read type expression
and do corresponding actions at second-pass.")

(comment "Concerning record:"
         "- read [:record [['f1 't1] ['f2 't2] ...]] into a type
structure;"
         "- attach the type structure to a type;"
         "- match given field name and field expression to
corresponding field name and field type;"
         "- get corresponding type of a given field name.")

(comment "Concerning array:"
         "- read [:array 'tid] into a type structure;"
         "- attach the type structure to a type;"
         "- match given type to array element type;"
         "- get the element type.")

(defn read-ty-fields [env fieldv]
  (loop [fs (seq fieldv) fv [] s #{}]
    (if (empty? fs)
      fv
      (let [[name tid] (first fs)
            type (get (:ty-id env) tid)]
        (assert type "field expect existing type")
        (assert (not (contains? s name))
                "duplicate field name found")
        (recur (rest fs)
               (conj fv {:name name :type type})
               (conj s name))))))

(defn cons-record
  "construct a record type structure from the given ty-expression
  and attach it to the existing type x"
  [x rec-ty-expr env]
  (let [label (rec-ty-expr 0)]
    (assert (= label :record) "expect record type expression")
    (let [fv (rec-ty-expr 1)
          st {:kind :record
              :fieldv (read-ty-fields env fv)}]
      (attach-struct x st))))

(defn record? [x]
  (let [rx (find-set x)]
    (if-let [st (:struct @rx)]
      (= (:kind (force (st))) :record)
      false)))

(defn get-record-fieldv
  "return [['f1 't1] ['f2 't2] ...] for the given record"
  [x]
  (let [rx (find-set x)
        st (:struct @rx)
        fv (:fieldv (force (st)))]
    (loop [v [] fs (seq fv)]
      (if (empty? fs)
        v
        (let [{nm :name ty :type} (first fs)]
          (recur (conj v [nm ty]) (rest fs)))))))

(defn get-record-field-type
  "return field type for the field name of the given record type"
  [x fdnm]
  (let [rx (find-set x)
        st (:struct @rx)
        fv (:fieldv (force (st)))]
    (loop [fs (seq fv)]
      (when-let [f (first fs)]
        (if (= (:name f) fdnm)
          (:type f)
          (recur (rest fs)))))))

(defn cons-array
  "construct an array type structure from the given ty-expression
  and attach it to the existing type x"
  [x arr-ty-expr env]
  (let [label (arr-ty-expr 0)]
    (assert (= label :array) "expect array type expression")
    (let [etid (arr-ty-expr 1)
          et (get (:ty-id env) etid)]
      (assert et (str etid " is not an existing type here"))
      (let [st {:kind :array :elem-type et}]
        (attach-struct x st)))))

(defn array? [x]
  (let [rx (find-set x)]
    (if-let [st (:struct @rx)]
      (= (:kind (force (st))) :array)
      false)))

(defn get-array-elem-type
  "return element type for the given array"
  [x]
  (let [rx (find-set x)
        st (:struct @rx)]
    (:elem-type (force (st)))))
