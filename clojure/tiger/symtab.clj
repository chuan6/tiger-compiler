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
           (conj (pop stack)
                 (assoc top sym entity)))))

(defn update-at-curr-scope
  "introduce or update a property of entity of an existing entry"
  [env namespace sym property value]
  (assert (and (#{:ty-id :id} namespace)
               (symbol? sym)))
  (let [stack (get env namespace)
        top   (peek stack)
        entry (find top sym)]
    (assert (not (nil? entry)))
    (->> value
         (assoc (val entry) property)
         (assoc top sym)
         (conj (pop stack))
         (assoc env namespace))))

(defn nest-scope
  "create a empty nested scope for given namespace at given env"
  [env namespace]
  (assert (#{:ty-id :id} namespace))
  (assoc env namespace
         (conj (get env namespace) {})))
