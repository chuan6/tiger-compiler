(ns semantics)

(defn doit [env & args]
  (case (first args)
    :create-ty (apply do-create-ty env (rest args))))

(defn do-create-ty [env kind & args]
  (case kind
    :record
    (let [xv (first args) n (count xv)]
      (loop [i  0
             s  #{}
             yv []
             f  false]
        (if (= i n)
          (do (assert (not f) "field names are not unique")
              yv)
          (let [x  (xv i)
                xa (x 0)
                xb (x 1)]
            (assert (symtab/type-in-scope? env xb))
            (recur (inc i)
                   (conj s xa)
                   (conj yv {:field-name xa :field-type xb})
                   (or f (contains? s xa)))))))))

(defn do-ty-decl [env tid texpr]
  (let [fieldv (apply doit env texpr)]
    (symtab/create-an-entry (:ty-id env) tid {:kind :record :fields fieldv})))
