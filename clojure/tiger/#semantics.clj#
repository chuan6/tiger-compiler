(ns semantics)

(comment :type-checking "
  In Tiger, a type is attached to every expression, no matter the expression
returns a value or not. An expression that doesn't return a value is of type
'void.
  Besides 'void, Tiger has two primitive types: 'int, and 'string.
  Tiger supports constructing complex types from simpler ones, by two
constructors: array, and record. A type constructed by record can be nil.
  A type constructed by array or record is a pair, a symobl that refers to the
type, and an entity that holds structure of the type. An array entity holds a
symbol that refers to the element type. While a record entity holds a sequence
of fields; each consists of a symbol of the field and a symbol of the field's
type.
  Tiger also supports type aliasing. A new type can be created simply by
referring to another type, by name. A value of the aliasing type can be assigned
to a variable of the original type.
")

(def type-kinds #{:int :string :void :nil :array :record :alias})
(def ty-int {:kind :int})
(def ty-string {:kind :string})
(def ty-nil {:kind :nil})
(def ty-void {:kind :void})
(defn cons-type [kind & args]
  (case kind
    :array  (let [[s et] args] {:name s :kind :array  :elem-type et})
    :record (let [[s fs] args] {:name s :kind :record :fields fs})
    :alias  (let [[s s'] args] {:name s :kind :alias  :origin s'})))

(defn kind-of-type [t] (type-kinds (:kind t)))

(defn lookup [env sym]
  (loop [stack env]
    (if (empty? stack)
      nil
      (let [scope (peek stack) v (get scope sym)]
        (if v
          {:env stack :val v}
          (recur (pop stack)))))))

(defn bind [env sym item]
  (let [stack env
        scope (peek stack)]
    (conj (pop stack)
          (assoc scope sym item))))

(defn alias-type-of [ty-env s s']
  (let [{env :env ta :val} (lookup ty-env s)]
    (if (= (kind-of-type ta) :alias)
      (let [ta-from (:origin ta)]
        (if (= ta-from s')
          true
          (alias-type-of env ta-from s')))
      false)))

(declare type-of)

(defn assignable? [env ty-env e1 e2]
  (let [ta (type-of env ty-env e1) kta (kind-of-type ta)
        tb (type-of env ty-env e2) ktb (kind-of-type tb)]
    (and (not (= ktb :void))
         (or (or (and (= kta :record) (= ktb :nil))
                 (= kta ktb :int)
                 (= kta ktb :string))
             (= (:name ta) (:name tb))))))

(defn typeof-assign [env ty-env lval expr]
  (assert (assignable env ty-env lval expr))
  ty-void)

(defn typeof-empty [env ty-env] ty-void)

(defn typeof-let
  ([env ty-env decl-list] ty-void)
  ([env ty-env decl-list expr-seq]
   (let [{env' :env ty-env' :ty-env} (read-decl-list env ty-env decl-list)
         env (conj env env')
         ty-env (conj ty-env ty-env')]
     (typeof-expr-seq env ty-env expr-))))

(defn type-check [node]
  (let [expr-set #{:assign :empty :create-tmp :if
                   :while :for :let :lvalue :exprs
                   :neg :or :and :cmp :string :cal :int
                   :nil :call :assign-fields}
        decl-set #{:ty-decl :var-decl :fn-decl
                   :consec-ty-decl :consec-fn-decl
                   :create-ty :ty-assoc}
        label (node 0)]
    (cond
      (expr-set label) ())))

(defn type-of [node]
  (case (node 0)
    :assign
    :empty
    :create-tmp
    :if
    :while
    :for
    :let
    :lvalue
    :exprs
    :neg
    :or
    :and
    :cmp
    :string
    :cal
    :int
    :nil
    :call
    :assign-fields))

(defn new-env [node]
  (case (node 0)
    :ty-decl
    :var-decl
    :fn-decl
    :consec-ty-decl
    :consec-fn-decl
    :create-ty
    :ty-assoc
    ))
