(ns semantics)

(declare doit)

(def empty-env {:ty-id [] :id []})
(def empty-scope {:ty-id {} :id {}})

(defn push-scope
  "nest a scope, and return updated env"
  [env scope]
  (let [{id-stack :id ty-id-stack :ty-id} env
        {id-scope :id ty-id-scope :ty-id} scope]
    {:id    (conj id-stack id-scope)
     :ty-id (conj ty-id-stack ty-id-scope)}))

(defn pop-scope
  "leave innermost scope, and return updated env"
  [env]
  (let [{id-stack :id ty-id-stack :ty-id} env]
    (assert (= (count id-stack) (count ty-id-stack)))
    (if (empty? id-stack)
      env
      {:id (pop id-stack) :ty-id (pop ty-id-stack)})))

(defn peek-scope
  "get the innermost scope"
  [env]
  (let [{id-stack :id ty-id-stack :ty-id} env]
    (assert (= (count id-stack) (count ty-id-stack)))
    (if (empty? id-stack)
      nil
      {:id (peek id-stack) :ty-id (peek ty-id-stack)})))

(defn assoc-id
  "assoc an id entry, and return updated scope"
  [scope k v] (assoc scope :id (assoc (:id scope) k v)))

(defn assoc-ty-id
  "assoc a ty-id entry, and return updated scope"
  [scope k v] (assoc scope :ty-id (assoc (:ty-id scope) k v)))

(defn lookup-id
  "find the id entry in the innermost scope, return its entity and env"
  [env id]
  (loop [env env]
    (let [top (peek-scope env)]
      (if (nil? top)
        nil ;"no such id"
        (let [entity (get (:id top) id)]
          (if entity
            {:result entity :env env}
            (recur (pop-scope env))))))))

(defn lookup-ty-id
  "find the ty-id entry in the innermost scope, return its entity and env"
  [env ty-id]
  (loop [env env]
    (let [top (peek-scope env)]
      (if (nil? top)
        nil ;"no such ty-id"
        (let [entity (get (:ty-id top) ty-id)]
          (if entity
            {:result entity :env env}
            (recur (pop-scope env))))))))

(defn do-assign [env lvalue expr] {:kind :void})
(defn do-empty [env] {:kind :void})
(defn do-record [env tname texpr] {:kind :record})
(defn do-array [env tname len val] {:kind :array})
(defn do-if [env cond then & args] )
(defn do-while [env cond loop] {:kind :void})
(defn do-for [env iname begin end loop] {:kind :void})
(defn do-break [env])
(defn do-let [env decls & seq])
(defn do-lvalue [env kind & args])
(defn do-neg [env x] {:kind :int})
(defn do-or [env x y] {:kind :int})
(defn do-and [env x y] {:kind :int})
(defn do-string [env s] {:kind :string})
(defn do-cmp [env kind x y] {:kind :int})
(defn do-int [env d] {:kind :int})
(defn do-cal [env kind x y])
(defn do-nil [env] {:kind :nil})
(defn do-seq [env seq])
(defn do-call [env fname & args])

(defn consec-ty-decl-1st-pass
  "add headers to scope"
  [env decl-vec]
  (loop [scope empty-scope
         ds (seq decl-vec)
         s #{}]
    (if (empty? ds)
      (push-scope env scope)
      (let [[label header] (first ds)]
        (assert (= label :ty-decl))
        (assert (not (contains? s header)))
        (recur (assoc-ty-id scope header :undefined)
               (rest ds)
               (conj s header))))))

(defn do-ty-fields
  "return a vector of type field entities"
  [env fv]
  (loop [fs (seq fv) fv [] s #{}]
    (if (empty? fs) fv
        (let [[name type] (first fs)]
          (assert (lookup-ty-id env type))
          (assert (not (contains? s name)))
          (recur (rest fs)
                 (conj fv {:name name :type type})
                 (conj s name))))))

;;e.g. (-> [] (f 'a 'b) (f 'b 'd) (f 'c 'a) (f 'd 'a))
;;will return nil because there is redundant alias declartion
(defn collect-alias-sets [asv x y]
  (let [n (count asv)]
    (loop [i 0 ix -1 iy -1]
      (if (= i n)
        (cond
          (= ix iy -1) (conj asv #{x y})
          (= ix -1)    (assoc asv iy (conj (asv iy) x))
          (= iy -1)    (assoc asv ix (conj (asv ix) y))
          (= ix iy)    nil ;redundant alias declaration is found
          :merge-sets  (loop [asv' [(clojure.set/union
                                           (asv ix) (asv iy))]
                              i 0]
                         (if (= i n) asv'
                             (if (or (= i ix) (= i iy))
                               (recur asv' (inc i)) ;skip
                               (recur (conj asv' (asv i)) (inc i))))))
        (let [aset (asv i)]
          (recur (inc i)
                 (if (aset x)
                   (do (assert (= ix -1)) i) ;x can only be found in one set
                   ix)
                 (if (aset y)
                   (do (assert (= iy -1)) i) ;y can only be found in one set
                   iy)))))))

(defn consec-ty-decl-2nd-pass
  "assoc bodies to headers in the scope, and collect alias-set-coll"
  [env decl-vec]
  (loop [scope (peek-scope env)
         asv   []
         ds    (seq decl-vec)]
    (if (empty? ds)
      (-> (pop-scope env) (push-scope scope)
          (assoc :alias-set-coll asv))
      (let [[label header body] (first ds)]
        (assert (= label :ty-decl))
        (assert (get (:ty-id scope) header))
        (let [[kind ty] body]
          (case kind
            :alias
            (let [orig-t ty]
              (assert (lookup-ty-id env orig-t))
              (let [asv (collect-alias-sets asv header orig-t)]
                (assert asv "redundant alias declaration is found")
                (recur (assoc-ty-id scope header (type/alias orig-t))
                       asv (rest ds))))

            :array
            (let [elem-t ty]
              (assert (lookup-ty-id env elem-t))
              (recur (assoc-ty-id scope header (type/array elem-t))
                     asv (rest ds)))

            :record
            (let [fv ty]
              (recur (assoc-ty-id scope header
                                  (type/record (do-ty-fields env fv)))
                     asv (rest ds)))))))))

(defn update-a-ty-id-entry [env id k v]
  (loop [s env
         t empty-env]
    (let [scope (peek-scope s)]
      (if (nil? scope)
        env
        (let [entity (get (:ty-id scope) id)]
          (if (nil? entity)
            (recur (pop-scope s)
                   (push-scope t scope))
            (let [scope (assoc-ty-id scope
                                     id
                                     (assoc entity k v))]
              (loop [r (-> (pop-scope s) (push-scope scope))
                     t t]
                (let [scope (peek-scope t)]
                  (if (nil? scope)
                    r
                    (recur (push-scope r scope)
                           (pop-scope t))))))))))))

(defn form-equiv-set [env aset]
  (loop [es (seq aset)
         r  {}]
    (if (empty? es)
      r
      (let [e (first es)
            env' (:env (lookup-ty-id env e))]
        (assert (not (nil? env')))
        (recur (rest es) (assoc r e env'))))))

(defn consec-ty-decl-3rd-pass [env]
  (let [asv (:alias-set-coll env)]
    (assert (not (nil? asv)))
    (loop [env (dissoc env :alias-set-coll)
           as  (seq asv)]
      (if (empty? as)
        env
        (let [a (first as)
              es (form-equiv-set env a)]
          (recur
           (loop [env env
                  ts (seq a)]
             (if (empty? ts)
               env
               (let [t (first ts)]
                 (recur (update-a-ty-id-entry env t :equiv-set es)
                        (rest ts)))))
           (rest as)))))))

(defn do-consec-ty-decl [env & args]
  (let [dv (first args)]
    (-> env
        (consec-ty-decl-1st-pass dv)
        (consec-ty-decl-2nd-pass dv)
        (consec-ty-decl-3rd-pass))))

(defn do-var-decl
  "assoc variable id to current scope"
  ([env var expr]
   (let [t (apply doit env expr)]
     (assert (not (type/void? (:result (lookup-ty-id (:env t) (:name t))))))
     (let [scope (peek-scope env)]
       (assert (not (nil? scope)))
       (push-scope (pop-scope env)
                   (assoc-id scope var t)))))
  ([env var type expr]))

(defn do-consec-fn-decl [env & args])

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
    :consec-fn-decl (apply do-consec-fn-decl env (rest args))))

