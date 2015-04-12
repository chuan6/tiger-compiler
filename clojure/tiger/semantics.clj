(ns semantics)

(declare doit)

(defn do-create-ty [env kind & args]
  (case kind
    :record
    (let [xv (first args), n (count xv)]
      (loop [yv []
             f  false
             s  #{}
             i  0]
        (if (= i n)
          (do (assert (not f) "field names are not unique") yv)
          (let [x (xv i), xa (x 0), xb (x 1)]
            (assert (symtab/type-in-scope? env xb)
                    (str "field type " xb " is not defined"))
            (recur (conj yv {:name xa :type xb})
                   (or f (contains? s xa))
                   (conj s xa)
                   (inc i))))))))

(defn do-ty-decl [env tid texpr]
  (let [fieldv (apply doit env texpr)]
    (symtab/create-an-entry env :ty-id tid {:kind :record :fields fieldv})))

(defn do-consec-ty-decl [env & args]
  (let [declv (first args), n (count declv)]
    (let [env (loop [r env
                     f false
                     s #{}
                     i 0] ;first pass, collecting headers
                (if (= i n)
                  (do (assert (not f)
                              "type names in consec-ty-decl are not unique")
                      r)
                  (let [ty-name ((declv i) 1)]
                    (recur (symtab/create-an-entry r :ty-id ty-name :undefined)
                           (or f (contains? s ty-name))
                           (conj s ty-name)
                           (inc i)))))]
      (loop [r env, i 0] ;second pass, appending bodies
        (if (= i n)
          r
          (recur (apply doit r (declv i)) (inc i)))))))

(defn doit [env & args]
  (case (first args)
    :create-ty (apply do-create-ty env (rest args))
    :ty-decl (apply do-ty-decl env (rest args))))
