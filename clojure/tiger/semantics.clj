(ns semantics)

(declare doit)

(defn assoc-tid [env tid entity]
  (assert (not (or (= tid 'int) (= tid 'string))))
  (let [prev (:ty-id env)]
    (assoc env :ty-id (assoc prev tid entity))))

(defn declared-tid? [env tid]
  (contains? (:ty-id env) tid))

(defn lookup-tid [env tid] (get (:ty-id env) tid))

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

