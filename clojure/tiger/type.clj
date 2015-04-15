(ns type)

(def kind-set #{:void :int :string :nil :record :array :alias})

(defn create [kind ])

(defn alias-equal? [ta tb]
  (let [ta-entity (val ta)
        tb-entity (val tb)]
    (assert (= (:kind ta-entity) (:kind tb-entity) :alias))
    (let [aflag ((:equiv-set ta-entity) (key tb))
          bflag ((:equiv-set tb-entity) (key ta))]
      (assert (= aflag bflag))
      aflag)))

(defn equal? [ta tb]
  (let [ta-name (key ta) ta-kind (:kind (val ta))
        tb-name (key tb) tb-kind (:kind (val tb))]
    ))
