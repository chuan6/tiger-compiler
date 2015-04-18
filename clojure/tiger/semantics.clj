(ns semantics)

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
            {:result entity :environment env}
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
            {:result entity :environment env}
            (recur (pop-scope env))))))))

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

(defn do-consec-ty-decl [env & args]
  (let [dv (first args)]))

(defn doit [env & args]
  (case (first args)
    :consec-ty-decl (apply do-consec-ty-decl env (rest args))))

