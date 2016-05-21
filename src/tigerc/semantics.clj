(ns tigerc.semantics
  (:require [tigerc.type :as type]))

(def init-env
  {:ty-id {'int type/int 'string type/string}
   :id {'print     {:kind :procedure
                    :params [{:name 's :type type/string}]}
        'printi    {:kind :procedure
                    :params [{:name 'i :type type/int}]}
        'flush     {:kind :procedure
                    :params []}
        'getchar   {:kind :function
                    :return type/string
                    :params []}
        'ord       {:kind :function
                    :return type/int
                    :params [{:name 's :type type/string}]}
        'chr       {:kind :function
                    :return type/string
                    :params [{:name 'i :type type/int}]}
        'size      {:kind :function
                    :return type/int
                    :params [{:name 's :type type/string}]}
        'substring {:kind :function
                    :return type/string
                    :params [{:name 's :type type/string}
                             {:name 'f :type type/int}
                             {:name 'n :type type/int}]}
        'concat    {:kind :function
                    :return type/string
                    :params [{:name 's1 :type type/string}
                             {:name 's2 :type type/string}]}
        'not       {:kind :function
                    :return type/int
                    :params [{:name 'i :type type/int}]}
        'exit      {:kind :procedure
                    :params [{:name 'i :type type/int}]}}})

(declare do-expression)

(defn assoc-id [env id entity]
  (assert (#{:variable   ;l-value
             :loop-index ;for-loop index
             :procedure  ;call with no return
             :function   ;call with return
             } (:kind entity))
          "unknown kind of entity")
  (let [prev (:id env)]
    (assoc env :id (assoc prev id entity))))

(defn assoc-tid [env tid entity]
  (assert (not (or (= tid 'int) (= tid 'string))))
  (let [prev (:ty-id env)]
    (assoc env :ty-id (assoc prev tid entity))))

(defn assoc-params [env params]
  (let [assoc-param (fn [env param]
                      (assoc-id env (:name param)
                                {:kind :variable
                                 :type (:type param)}))]
    (reduce assoc-param env params)))

(defn declared-tid? [env tid]
  (contains? (:ty-id env) tid))

(defn lookup-id [env id] (get (:id env) id))
(defn lookup-tid [env tid] (get (:ty-id env) tid))

(defn do-consec-fn-decl [env-stack & fn-decl-vec]
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
                    [action void? id] d
                    fenv (assoc-params env (:params (lookup-id env id)))]
                (if void?
                  (let [body (d 4)
                        t (do-expression fenv body)]
                    (assert (type/void? t)
                            "procedure body must not return value")
                    (recur (rest ds)))
                  (let [[ret body] (subvec d 4)
                        tr (lookup-tid env ret)
                        t (do-expression fenv body)]
                    (assert (type/equal? tr t)
                            "function body isn't of the return type")
                    (recur (rest ds))))))))]
    (conj env-stack (-> env (first-pass) (second-pass)))))

(defn do-consec-ty-decl [env-stack & ty-decl-vec]
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

        second-pass ;attach type structures
        (fn [env] ;note: change through side-effects
          (loop [ds ds]
            (if (empty? ds)
              env
              (let [[action header body] (first ds)
                    kind (body 0)
                    a (lookup-tid env header)]
                (do (case kind
                      :alias  (let [b (lookup-tid env (body 1))]
                                (assert b (str (body 1) " is not an"
                                               "existing type"))
                                (type/let-equal b a))
                      :array  (type/cons-array a body env)
                      :record (type/cons-record a body env))
                    (recur (rest ds)))))))

        third-pass ;check if every type name has a type struct attached
        (fn [env]
          (loop [ds ds]
            (if (empty? ds)
              env
              (let [header ((first ds) 1)
                    a (lookup-tid env header)]
                (assert (or (type/int? a) (type/string? a)
                            (type/struct-attached? a))
                        (str "type " header " is not realized" env))
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
    type/int))

(defn do-or [env a b]
  (let [tya (do-expression env a)
        tyb (do-expression env b)]
    (assert (and (type/int? tya) (type/int? tyb))
            "| only works on integers")
    type/int))

(defn do-and [env a b]
  (let [tya (do-expression env a)
        tyb (do-expression env b)]
    (assert (and (type/int? tya) (type/int? tyb))
            "& only works on integers")
    type/int))

(defn do-cmp [env kind a b]
  (let [tya (do-expression env a)
        tyb (do-expression env b)]
    (assert (not (or (type/void? tya) (type/void? tyb)))
            "cannot compare against no-value expression")
    (assert (type/equal? tya tyb)
            "cannot compare between expressions of different types")
    (if (#{:eq :neq} kind)
      type/int
      (do (assert (or (type/int? tya) (type/string? tya))
                  "<, >, <=, >= only work on integers or strings")
          type/int))))

(defn do-string [env val] type/string)

(defn do-cal [env kind a b]
  (let [tya (do-expression env a)
        tyb (do-expression env b)]
    (assert (and (type/int? tya) (type/int? tyb))
            "+, -, *, / only work on integers")
    type/int))

(defn do-int [env val] type/int)

(defn do-nil [env] type/nil-expr)

(defn do-record [env tid fv]
  (let [t (lookup-tid env tid)]
    (assert (type/record? t) (str "expect " t " to be record"))
    (let [template (type/get-record-fieldv t)]
      (assert (= (count fv) (count template))
              "number of fields doesn't match")
      (loop [fs (seq fv) ts (seq template)]
        (if (empty? fs)
          t
          (let [[fn expr] (first fs)
                et (do-expression env expr)
                [nm ty] (first ts)]
            (assert (= fn nm) "field name doesn't match")
            (assert (type/equal? ty et) "field type doesn't match")
            (recur (rest fs) (rest ts))))))))

(defn do-array [env tid len init]
  (let [t (lookup-tid env tid)]
    (assert (type/array? t) (str "expect " t " to be array"))
    (let [tylen (do-expression env len)
          tyelem (type/get-array-elem-type t)
          tyinit (do-expression env init)]
      (assert (type/int? tylen) "found non-integer array length")
      (assert (type/equal? tyelem tyinit)
              "array element type doesn't match")
      t)))

(defn do-let [env decl-list expr-seq]
  (let [env-stack
        (loop [estk [env]
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
                 :consec-fn-decl
                 (apply do-consec-fn-decl estk (subvec d 1))))
             (rest ds))))
        env (peek env-stack)]
    (println "let environment: " env)
    (loop [es (seq expr-seq)
           t type/void]
      (if (empty? es)
        t
        (recur (rest es) (do-expression env (first es)))))))

(defn do-empty [env] type/void)

(defn do-lvalue [env kind & args]
  (case kind
    :simple
    (let [id (first args)
          entity (lookup-id env id)]
      (assert (and entity (contains? entity :type)) (str id env))
      (:type entity))

    :field
    (let [[prefix fdn] args
          t (do-expression env prefix)]
      (assert (type/record? t)
              "cannot access field of a non-record value")
      (let [fdt (type/get-record-field-type t fdn)]
        (assert (not (nil? fdt)) "no such field name for the type")
        fdt))

    :subscript
    (let [[prefix idx] args
          t (do-expression env prefix)]
      (assert (type/array? t)
              "cannot access by index for a non-array value")
      (let [elmt (type/get-array-elem-type t)
            ti (do-expression env idx)]
        (assert (type/int? ti) "expect array index to be an integer")
        elmt))))

(defn do-assign [env lval expr]
  (let [assign-to-loop-index?
        (fn []
          (if (= (lval 1) :simple) ;loop index is a :simple var
            (let [id (lval 2)
                  entity (lookup-id env id)]
              (= (:kind entity) :loop-index))
            false))]
    (assert (not (assign-to-loop-index?))
            "for-loop index must NOT be assigned to")
    (let [ta (do-expression env lval)
          tb (do-expression env expr)]
      (assert (type/equal? ta tb))
      type/void)))

(defn do-seq [env expr-seq]
  (loop [es (seq expr-seq)
         t type/void]
    (if (empty? es)
      t
      (recur (rest es) (do-expression env (first es))))))

(defn do-if
  ([env cond then]
   (let [t (do-expression env cond)
         ta (do-expression env then)]
     (assert (type/int? t) "cond-expr must be of int type")
     (assert (type/void? ta) then)
     type/void))
  ([env cond then else]
   (let [t (do-expression env cond)]
     (assert (type/int? t) "cond-expr must be of int type")
     (let [ta (do-expression env then)
           tb (do-expression env else)]
       (assert (type/equal? ta tb)
               "types of then-expr and eles-expr don't match")
       (if (type/void? ta)
         type/void
         (let [fa (= ta type/nil-expr)
               fb (= tb type/nil-expr)]
           (case [fa fb]
             [true true] type/nil-expr
             [true false] tb
             [false true] ta
             [false false] ta)))))))

(defn do-while [env cond loop]
  (let [tc (do-expression env cond)
        t (do-expression env loop)]
    (assert (type/int? tc) "cond-expr must be of int type")
    (assert (type/void? t) "loop-expr must produce no value")
    type/void))

(defn do-for [env id from to loop]
  (let [ta (do-expression env from)
        tb (do-expression env to)]
    (assert (and (type/int? ta) (type/int? tb))
            "loop index range must be of int type")
    (let [loop-env (assoc-id env id {:kind :loop-index :type type/int})
          t (do-expression loop-env loop)]
      (assert (type/void? t) "loop-expr must produce no value")
      type/void)))

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
                  (let [a (first as)
                        ta (do-expression env a)]
                    (do (assert (type/equal? (:type p) ta)
                                "argument type doesn't match")
                        (recur (rest ps) (rest as)))))))
            type/void)
        :function
        (do (let [pv (:params entity)
                  av expr-list]
              (assert (= (count pv) (count av))
                      (str "argument number doesn't match " id))
              (loop [ps (seq pv) as (seq av)]
                (when-let [p (first ps)]
                  (let [a (first as)
                        ta (do-expression env a)]
                    (do (assert (type/equal? (:type p) ta)
                                "argument type doesn't match")
                        (recur (rest ps) (rest as)))))))
            (:return entity))))))

;;TODO do-break

(defn do-expression [env expr]
  (let [f (case (expr 0)
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

