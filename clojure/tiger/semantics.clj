(ns semantics)

(declare do-expression)

(defn assoc-id [env id entity]
  (let [prev (:id env)]
    (assoc env :id (assoc prev id entity))))

(defn assoc-tid [env tid entity]
  (assert (not (or (= tid 'int) (= tid 'string))))
  (let [prev (:ty-id env)]
    (assoc env :ty-id (assoc prev tid entity))))

(defn declared-tid? [env tid]
  (contains? (:ty-id env) tid))

(defn lookup-id [env id] (get (:id env) id))
(defn lookup-tid [env tid] (get (:ty-id env) tid))

(defn do-consec-fn-decl [env-stack fn-decl-vec]
  (let [env (peek env-stack)
        ds (seq fn-decl-vec)

        first-pass ;collect headers, and init func definitions
        (fn [env]
          (loop [env env ds ds s #{}]
            (if (empty? ds)
              env
              (let [d (first ds)
                    [action void? id params] d]
                (assert (= action :fn-decl))
                (assert (not (contains? s id))
                        (str "duplicated declaration of function " id))
                (let [formal-params (type/read-ty-fields env params)
                      entity
                      (if void?
                        {:kind :procedure :params formal-params}
                        (let [ret (d 4)
                              t (lookup-tid env ret)]
                          (assert (not (nil? t))
                                  (str "non-exist return type " ret))
                          {:kind :function :return t
                           :params formal-params}))]
                  (recur (assoc-id env id entity)
                         (rest ds) (conj s id)))))))

        second-pass ;type check function body
        (fn [env]
          (loop [ds ds]
            (if (empty? ds)
              env
              (let [d (first ds)
                    [action void?] d]
                (if void?
                  (let [body (d 4)
                        t (do-expression env body)]
                    (assert (type/void? t)
                            "procedure body must not return value")
                    (rest ds))
                  (let [[ret body] (subvec d 4)
                        tr (lookup-tid env ret)
                        t (do-expression env body)]
                    (assert (type/equal? tr t)
                            "function body isn't of the return type")
                    (rest ds)))))))]
    (conj env-stack (-> env (first-pass) (second-pass)))))

(defn do-consec-ty-decl [env-stack ty-decl-vec]
  (let [env (peek env-stack)
        ds (seq ty-decl-vec)

        first-pass ;collect headers, and init types
        (fn [env]
          (loop [env env ds ds s #{}]
            (if (empty? ds)
              env
              (let [[action header] (first ds)]
                (assert (= action :ty-decl))
                (assert (not (contains? s header))
                        (str "duplicate declaration of " header
                             " is found"))
                (recur (assoc-tid env header (type/init))
                       (rest ds) (conj s header))))))

        second-pass ;attach type entities
        (fn [env] ;note: change through side-effects
          (loop [ds ds]
            (if (empty? ds)
              env
              (let [[action header body] (first ds)
                    a (lookup-tid env header)]
                (do (if-let [entity (type/expr env body)]
                      ;;type is defined by a concrete type
                      (type/attach-entity a entity)
                      ;;type is an alias of a non-built-in type
                      (let [b (lookup-tid env (body 1))]
                        (type/let-equal a b)))
                    (recur (rest ds)))))))

        third-pass ;check if every type name has a type entity attached
        (fn [env]
          (loop [ds ds]
            (if (empty? ds)
              env
              (let [header ((first ds) 1)
                    a (lookup-tid env header)]
                (assert (type/entity-attached? a))
                (recur (rest ds))))))]
    (conj env-stack (-> env (first-pass) (second-pass) (third-pass)))))

(defn do-var-decl
  ([env-stack id expr]
   (let [env (peek env-stack)
         et (do-expression env expr)]
     (assert (not (type/void? et)))
     (conj env-stack (assoc-id env id {:kind :variable :type et}))))

  ([env-stack id type expr]
   (let [env (peek env-stack)
         t (lookup-tid env type)]
     (assert (not (nil? t)))
     (let [et (do-expression env expr)]
       (assert (type/equal? t et))
       (conj env-stack (assoc-id env id {:kind :variable :type t}))))))

(defn do-neg [env val]
  (let [t (do-expression env val)]
    (assert (type/int? t) "unary - only works on integer")
    (lookup-tid env 'int)))

(defn do-or [env a b]
  (let [tya (do-expression env a)
        tyb (do-expression env b)]
    (assert (and (type/int? tya) (type/int? tyb))
            "| only works on integers")
    (lookup-tid env 'int)))

(defn do-and [env a b]
  (let [tya (do-expression env a)
        tyb (do-expression env b)]
    (assert (and (type/int? tya) (type/int? tyb))
            "& only works on integers")
    (lookup-tid env 'int)))

(defn do-cmp [env kind a b]
  (let [tya (do-expression env a)
        tyb (do-expression env b)]
    (assert (not (or (type/void? tya) (type/void? tyb)))
            "cannot compare against no-value expression")
    (assert (type/equal? tya tyb)
            "cannot compare between expressions of different types")
    (if (#{:eq :neq} kind)
      (lookup-tid env 'int)
      (do (assert (or (type/int? tya) (type/string? tya))
                  "<, >, <=, >= only work on integers or strings")
          (lookup-tid env 'int)))))

(defn do-string [env val] (lookup-tid env 'string))

(defn do-cal [env kind a b]
  (let [tya (do-expression env a)
        tyb (do-expression env b)]
    (assert (and (type/int? tya) (type/int? tyb))
            "+, -, *, / only work on integers")
    (lookup-tid env 'int)))

(defn do-int [env val] (lookup-tid env 'int))

(defn do-nil [env] type/nil-expr)

(defn do-record [env tid fv]
  (let [t (lookup-tid env tid)]
    (assert (type/record? t) (str "expect " t " to be record"))
    (let [template (:fieldv (type/get-entity t))]
      (assert (= (count fv) (count template))
              "number of fields doesn't match")
      (loop [fs (seq fv) ts (seq template)]
        (if (empty? fs)
          t
          (let [[fn expr] (first fs)
                et (do-expression env expr)
                {nm :name ty :type} (first ts)]
            (assert (= fn nm) "field name doesn't match")
            (assert (type/equal? ty et) "field type doesn't match")
            (recur (rest fs) (rest ts))))))))

(defn do-array [env tid len init]
  (let [t (lookup-tid env tid)]
    (assert (type/array? t) (str "expect " t " to be array"))
    (let [tylen (do-expression env len)
          tyelem (:elem-type (type/get-entity t))
          tyinit (do-expression env init)]
      (assert (type/int? tylen) "found non-integer array length")
      (assert (type/equal? tyelem tyinit)
              "array element type doesn't match")
      t)))

(defn do-let [env decl-list expr-seq]
  (let [env-stack (loop [estk [env]
                         ds (seq decl-list)]
                    (if (empty? ds)
                      estk
                      (recur
                       (let [d (first ds)]
                         (case (d 0)
                           :var-decl
                           (apply do-var-decl estk (subvec d 1))
                           :consec-ty-decl
                           (apply do-consec-ty-decl estk (subvec d 1))
                           ;;TODO :consec-fn-decl
                           ))
                       (rest ds))))
        env (peek env-stack)]
    (loop [es (seq expr-seq)
           t type/no-value]
      (if (empty? es)
        t
        (recur (rest es) (do-expression env (first es)))))))

(defn do-empty [env] type/no-value)

(defn do-lvalue [env kind & args]
  (case kind
    :simple
    (let [id (first args)
          entity (lookup-id env id)]
      (assert (and entity (contains? entity :type)))
      (:type entity))

    :field
    (let [[prefix fdn] args
          t (do-lvalue env prefix)]
      (assert (type/record? t)
              "cannot access field of a non-record value")
      (let [fdt (type/get-record-field (type/get-entity t) fdn)]
        (assert (not (nil? fdt)) "no such field name for the type")
        fdt))

    :subscript
    (let [[prefix idx] args
          t (do-lvalue env prefix)]
      (assert (type/array? t)
              "cannot access by index for a non-array value")
      (let [elmt (type/get-array-elem-type (type/get-entity t))
            ti (do-expression env idx)]
        (assert (type/int? ti) "expect array index to be an integer")
        elmt))))

(defn do-assign [env lval expr]
  (let [ta (do-lvalue env lval)
        tb (do-expression env expr)]
    (assert (type/equal? ta tb))
    ta))

(defn do-seq [env expr-seq]
  (loop [es (seq expr-seq)
         t type/no-value]
    (if (empty? es)
      t
      (recur (rest es) (do-expression env (first es))))))

(defn do-if
  ([env cond then]
   (let [t (do-expression env cond)
         ta (do-expression env then)]
     (assert (type/int? t) "cond-expr must be of int type")
     (assert (type/void? ta))
     type/no-value))
  ([env cond then else]
   (let [t (do-expression env cond)]
     (assert (type/int? t) "cond-expr must be of int type")
     (let [ta (do-expression env then)
           tb (do-expression env else)]
       (assert (type/equal? ta tb)
               "types of then-expr and eles-expr don't match")
       (if (type/void? ta)
         type/no-value
         (let [fa (= ta type/nil-expr)
               fb (= tb type/nil-expr)]
           (case [fa fb]
             [true true] type/nil-expr
             [true false] tb
             [false true] ta)))))))

(defn do-while [env cond loop]
  (let [tc (do-expression env cond)
        t (do-expression env loop)]
    (assert (type/int? tc) "cond-expr must be of int type")
    (assert (type/void? t) "loop-expr must produce no value")
    type/no-value))

;;TODO ensure that id is not assigned to in loop body
(defn do-for [env id from to loop]
  (let [ta (do-expression env from)
        tb (do-expression env to)]
    (assert (and (type/int? ta) (type/int? tb))
            "loop index range must be of int type")
    (let [loop-env (assoc-id env id
                             {:type (lookup-tid env 'int)})
          t (do-expression loop-env loop)]
      (assert (type/void? t) "loop-expr must produce no value")
      type/no-value)))

(defn do-call [env id expr-list]
  (let [entity (lookup-id env id)]
    (assert (not (nil? entity)) (str "cannot find id: " id))
    (let [kind (:kind entity)]
      (assert (#{:procedure :function} kind)
              (str id " is not a procedure or a function"))
      (case kind
        :procedure
        (do (let [pv (:params entity)
                  av expr-list]
              (assert (= (count pv) (count av))
                      (str "argument number doesn't match " id))
              (loop [ps (seq pv) as (seq av)]
                (when-let [p (first ps)]
                  (do (assert (type/equal? p (first as))
                              "argument type doesn't match")
                      (recur (rest ps) (rest as))))))
            type/no-value)
        :function
        (do (let [pv (:params entity)
                  av expr-list]
              (assert (= (count pv) (count av))
                      (str "argument number doesn't match " id))
              (loop [ps (seq pv) as (seq av)]
                (when-let [p (first ps)]
                  (do (assert (type/equal? p (first as))
                              "argument type doesn't match")
                      (recur (rest ps) (rest as))))))
            (:return entity))))))

(defn do-expression [env expr]
  (let [f (case (expr 0)
            :consec-ty-decl do-consec-ty-decl
            :var-decl do-var-decl
            :consec-fn-decl do-consec-fn-decl
            :assign do-assign
            :empty do-empty
            :array do-array
            :record do-record
            :seq do-seq
            :if do-if
            :while do-while
            :for do-for
            :let do-let
            :lvalue do-lvalue
            :neg do-neg
            :or do-or
            :and do-and
            :cmp do-cmp
            :nil do-nil
            :int do-int
            :cal do-cal
            :string do-string
            :call do-call)
        argv (subvec expr 1)]
    (apply f env argv)))

(comment
  (defn doit [env & args]
    (case (first args)
      :assign         (apply do-assign env (rest args))
      :empty          (apply do-empty env (rest args))
      :record         (apply do-record env (rest args))
      :array          (apply do-array env (rest args))
      :if             (apply do-if env (rest args))
      :while          (apply do-while env (rest args))
      :for            (apply do-for env (rest args))
      :break          (apply do-break env (rest args))
      :let            (apply do-let env (rest args))
      :lvalue         (apply do-lvalue env (rest args))
      :neg            (apply do-neg env (rest args))
      :or             (apply do-or env (rest args))
      :and            (apply do-and env (rest args))
      :string         (apply do-string env (rest args))
      :cmp            (apply do-cmp env (rest args))
      :int            (apply do-int env (rest args))
      :cal            (apply do-cal env (rest args))
      :nil            (apply do-nil env (rest args))
      :seq            (apply do-seq env (rest args))
      :call           (apply do-call env (rest args))
      :var-decl       (apply do-var-decl env (rest args))
      :consec-ty-decl (apply do-consec-ty-decl env (rest args))
      :consec-fn-decl (apply do-consec-fn-decl env (rest args)))))

