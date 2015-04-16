(ns semantics)

(declare doit)

(declare create-ty
         detect-redundant-ty-alias)

(defn do-ty-decl [env tid texpr]
  (let [entity (create-ty env tid texpr)]
    (->
     (if (type/alias? entity)
       (let [tmp (detect-redundant-ty-alias
                  (:alias-set-coll env)
                  (type/id entity)
                  (type/alias-origin entity))]
         (assert tmp "found redundant type aliasing in current consec-ty-decl")
         (assoc env :alias-set-coll tmp))
       env)
     (symtab/create-an-entry :ty-id tid entity))))

(declare consec-ty-decl-1st-pass
         consec-ty-decl-2nd-pass
         consec-ty-decl-3rd-pass)

(defn do-consec-ty-decl
  "form a new nested scope for this consecutive sequence of ty-decl's"
  [env & args]
  (let [declv (first args)]
    (-> env
        (consec-ty-decl-1st-pass declv)
        (consec-ty-decl-2nd-pass declv)
        (consec-ty-decl-3rd-pass))))

(defn do-var-decl
  ([env var expr]
   (let [et (apply doit env expr)]
     (assert (not (type/void? et)))
     (symtab/create-an-entry env :id var et)))
  ([env var type expr]))

(defn doit [env & args]
  (case (first args)
    :ty-decl (apply do-ty-decl env (rest args))
    :consec-ty-decl (apply do-consec-ty-decl env (rest args))))

(defn create-ty [env id expr]
  (let [arg (expr 1)]
    (case (expr 0)
      :alias
      (let [ot arg] ;the symbol for original type
        (assert (symtab/type-in-scope? env ot)
                (str "aliased original type " ot " is not defined"))
        (type/alias id ot))
      
      :record
      (let [xv arg, n (count xv)]
        (loop [yv []
               f  false
               s  #{}
               i  0]
          (if (= i n)
            (do (assert (not f) "field names are not unique")
                (type/record id yv))
            (let [x (xv i), xa (x 0), xb (x 1)]
              (assert (symtab/type-in-scope? env xb)
                      (str "field type " xb " is not defined"))
              (recur (conj yv {:name xa :type xb})
                     (or f (contains? s xa))
                     (conj s xa)
                     (inc i))))))

      :array
      (let [et arg] ;the symbol for element type
        (assert (symtab/type-in-scope? env et)
                (str "array element type " et " is not defined"))
        (type/array id et)))))

;;all sets in alias-set-vec should be exclusive
;;example:
;; > (-> [] (f 'a 'b) (f 'b 'd) (f 'c 'a) (f 'd 'a))
;; Error: redundant alias type declaration found
;; [#{a c b d}]
(defn detect-redundant-ty-alias [alias-set-vec x y]
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

(defn consec-ty-decl-1st-pass
  "introduce headers of type declarations to symbol table"
  [env decl-vec]
  (let [n (count decl-vec)]
    (loop [env (symtab/nest-scope env :ty-id)
           flag false, s #{} ;check for duplicated headers
           i 0]
      (if (= i n)
        (do (assert (= flag false)
                    "duplicate type names declared in consec-ty-decl")
            env)
        (let [ty-name ((decl-vec i) 1)]
          (recur (symtab/create-an-entry env :ty-id ty-name :undefined)
                 (or flag (contains? s ty-name))
                 (conj s ty-name)
                 (inc i)))))))

(defn consec-ty-decl-2nd-pass
  "appending bodies to corresponding headers that are already in table"
  [env decl-vec]
  (let [n (count decl-vec)]
    (loop [env (assoc env :alias-set-coll [])
           i 0]
      (if (= i n) env
          (recur (apply doit env (decl-vec i))
                 (inc i))))))

(defn consec-ty-decl-3rd-pass
  "utilize (:alias-set-coll env), and then drop it from env"
  [env]
  (let [ascoll (:alias-set-coll env)]
    (assert (not (nil? ascoll)))
    (loop [env env, ascoll (seq ascoll)]
      (if (empty? ascoll)
        (dissoc env :alias-set-coll)
        (recur (let [aset (first ascoll)]
                 (loop [env env, as (seq aset)]
                   (if (empty? as) env
                       (recur (symtab/update-at-curr-scope
                               env :ty-id (first as) :equiv-set aset)
                              (rest as)))))
               (rest ascoll))))))
