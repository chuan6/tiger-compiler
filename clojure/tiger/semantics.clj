(ns semantics)

(declare doit)

(defn do-create-ty [env kind & args]
  (case kind
    :alias
    (let [ot (first args)] ;the symbol for original type
      (assert (symtab/type-in-scope? env ot)
              (str "aliased original type " ot " is not defined"))
      {:kind :alias :orig-type ot})
    
    :record
    (let [xv (first args), n (count xv)]
      (loop [yv []
             f  false
             s  #{}
             i  0]
        (if (= i n)
          (do (assert (not f) "field names are not unique")
              {:kind :record :fields yv})
          (let [x (xv i), xa (x 0), xb (x 1)]
            (assert (symtab/type-in-scope? env xb)
                    (str "field type " xb " is not defined"))
            (recur (conj yv {:name xa :type xb})
                   (or f (contains? s xa))
                   (conj s xa)
                   (inc i))))))

    :array
    (let [et (first args)] ;the symbol for element type
      (assert (symtab/type-in-scope? env et)
              (str "array element type " et " is not defined"))
      {:kind :array :elem-type et})))

(defn detect-cyclic-aliasing [alias-set-vec x y]
  ;;all sets in alias-set-vec should be exclusive
  ;;example:
  ;; > (-> [] (f 'a 'b) (f 'b 'd) (f 'c 'a) (f 'd 'a))
  ;; Error: redundant alias type declaration found
  ;; [#{a c b d}]
  (let [asv alias-set-vec
        n (count asv)]
    (loop [i 0
           ix -1
           iy -1]
      (if (= i n)
        (cond (= ix iy -1) (conj asv #{x y})
              (= ix -1) (let [as (asv iy)]
                          (assoc asv iy (conj as x)))
              (= iy -1) (let [as (asv ix)]
                          (assoc asv ix (conj as y)))
              (= ix iy) nil
              :else (loop [asv' [(clojure.set/union (asv ix) (asv iy))]
                           i 1]
                      (if (= i n)
                        asv'
                        (if (or (= i ix) (= i iy))
                          (recur asv' (inc i))
                          (recur (conj asv' (asv i)) (inc i))))))
        (recur (inc i)
               (if (and (= ix -1) ((asv i) x)) i ix)
               (if (and (= iy -1) ((asv i) y)) i iy))))))

(defn do-ty-decl [env tid texpr]
  (let [entity (apply doit env texpr)
        tmp' (detect-cyclic-aliasing (:tmp env) tid (:orig-type entity))]
    (assert tmp' "found cyclic type aliasing in current consec-ty-decl")
    (-> (assoc env :tmp tmp')
        (symtab/create-an-entry :ty-id tid entity))))

(defn do-consec-ty-decl
  "form a new nested scope for this consecutive sequence of ty-decl's"
  [env & args]
  (let [declv (first args), n (count declv)]
    (let [env (loop [r (symtab/nest-scope env :ty-id)
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
      (loop [r (assoc env :tmp [])
             i 0] ;second pass, appending bodies
        (if (= i n)
          (dissoc r :tmp)
          (recur (apply doit r (declv i)) (inc i)))))))


(defn doit [env & args]
  (case (first args)
    :create-ty (apply do-create-ty env (rest args))
    :ty-decl (apply do-ty-decl env (rest args))))
