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
                   (fn [] (delay struct))))))

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

(defn read-ty-fields [env fields]
  (println fields)
  (loop [fs (seq fields) fv [] s #{}]
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
       :fieldv (read-ty-fields env body)})))

(defn get-array-elem-type
  [entity]
  (assert (= (:kind entity) :array))
  (assert (contains? entity :elem-type))
  (:elem-type entity))

(defn get-record-field
  [entity field]
  (assert (= (:kind entity) :record))
  (assert (contains? entity :fieldv))
  (loop [fds (seq (:fieldv entity))]
    (when-let [fd (first fds)]
      (if (= field (:name fd))
        (:type fd)
        (recur (rest fds))))))




