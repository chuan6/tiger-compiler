(ns semantics)

(declare doit)

(defn assoc-tid [env tid entity]
  (assert (or (or (not (= tid 'int)) (type/int? entity))
              (or (not (= tid 'string)) (type/string? entity))))
  (let [prev (:ty-id env)]
    (assoc env :ty-id (assoc prev tid entity))))

(defn declared-tid? [env tid]
  (contains? (:ty-id env) tid))

(defn lookup-tid [env tid] (get (:ty-id env) tid))

(defn do-consec-ty-decl [env-stack ty-decl-vec]
  (let [env (peek env-stack)
        ds (seq ty-decl-vec)]
    (conj
     env-stack
     (->
      env
      ((fn [env] ;1st pass: collect headers, and assoc each with :equiv-set
         (loop [ds ds env env s #{}]
           (if (empty? ds)
             env
             (let [[action header] (first ds)]
               (assert (= action :ty-decl))
               (assert (not (contains? s header))
                       (str "type name " s " is not unique in current"
                            " consecutive type declartions"))
               (recur (rest ds)
                      (assoc-tid env header
                                 {:equiv-set (disjoint-set/make-set header)})
                      (conj s header)))))))
      ((fn [env] ;2nd pass, updating alias equivalence sets
         (loop [ds ds env env]
           (if (empty? ds)
             env
             (let [[action header body] (first ds)
                   [kind arg] body]
               (assert (declared-tid? env header) (str header))
               (assert (contains? #{:alias :record :array} kind))
               (case kind
                 :alias
                 (recur
                  (rest ds)
                  (let [origin arg
                        ta (lookup-tid env header)
                        tb (lookup-tid env origin)
                        a (:equiv-set ta)
                        b (:equiv-set tb)]
                    (assert (and (disjoint-set/element? a)
                                 (disjoint-set/element? b)))
                    (do (disjoint-set/union a b)
                        ;;TODO guarantee that the ONLY non-alias element is at root
                        (assoc-tid env header (assoc ta :kind :alias)))))))))))))))

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

