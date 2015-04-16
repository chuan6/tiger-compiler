(ns type)

(def kind-set #{:void :int :string :nil :record :array :alias})

(defn alias [s t]
  (assert (and (symbol? s) (symbol? t)))
  (let [id (gensym (str s))]
    {:id id :kind :alias :orig-type t}))

(defn array [s t]
  (assert (and (symbol? s) (symbol? t)))
  (let [id (gensym (str s))]
    {:id id :kind :array :elem-type t}))

(defn record [s fv]
  (assert (and (symbol? s) (vector? fv)))
  (let [id (gensym (str s))]
    {:id id :kind :record :fieldv fv}))

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

(defn id [t] (:id t))

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
