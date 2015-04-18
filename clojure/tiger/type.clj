(ns type)

(def kind-set
  #{:void :int :string :nil :record :array :alias})

(defn id [s] (assert (symbol? s))
  (gensym (str s)))

(defn undefined [name] (assert (symbol? name))
  {:name name})

(defn alias [t] (assert (symbol? t))
  {:kind :alias :orig-type t})

(defn array [t] (assert (symbol? t))
  {:kind :array :elem-type t})

(defn record [fv] (assert (vector? fv))
  {:kind :record :fieldv fv})

(defn alias? [t] (= (:kind t) :alias))
(defn array? [t] (= (:kind t) :array))
(defn record? [t] (= (:kind t) :record))
(defn void? [t] (= (:kind t) :void))
(defn nil? [t] (= (:kind t) :nil))
(defn int? [t] (= (:kind t) :int))
(defn string? [t] (= (:kind t) :string))

(defn alias-origin [a]
  (assert (alias? a))
  (:orig-type a))

(defn equal? [ta tb]
  (or (= (:id ta) (:id tb))
      (and (nil? ta) (record? tb))
      (and (record? ta) (nil? tb))
      (let [ta-es (:equiv-set ta)
            tb-es (:equiv-set tb)]
        (if (or (= ta-es nil) (= tb-es nil))
          false
          (if (contains? ta-es (:id tb))
            (do (assert (contains? tb-es (:id ta)))
                true)
            false)))))
