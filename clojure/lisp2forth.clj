(ns forth)

;; e.g., from (* (+ 1 2) 3 4) to (4 (3 (2 1 +) *) *)
(defn norm [s]
  (if (or (number? s) (= (class s) clojure.lang.Symbol))
    s
    (if (seq? s)
      (if (<= (count s) 3) ;TODO inefficiency: need to go through list everytime
        (reverse (map norm s))
        (let [[op a b & more] s]
          (norm (conj more `(~op ~a ~b) op))))
      (println "Error: expect input to be a lisp expression, i.e., a list." (type s)))))

(defn to-forth [s]
  (flatten (norm s)))

