(ns symtab)

(defn type-in-scope?
  "determine if a type name can be found in the env"
  [env x]
  (let [stack (:ty-id env) n (count stack)]
    (loop [s stack, i 0]
      (if (= i n)
        false
        (if (get (peek s) x)
          true
          (recur (pop s) (inc i)))))))

(defn type-in-current-scope?
  [env x] true)

(defn create-an-entry
  "create an entry at current scope for given namespace (:ty-id or :id), and return updated env"
  [env namespace sym entity]
  (assert (and (#{:ty-id :id} namespace)
               (symbol? sym)))
  (let [stack (get env namespace)
        top   (peek stack)]
    (assoc env namespace
           (conj ()
                 (assoc top sym entity)))))
