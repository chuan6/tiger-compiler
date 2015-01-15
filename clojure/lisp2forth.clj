(ns forth)

(defn triplet
  ([list] (triplet () list 0))
  ([t ts c]
   (if (= c 3)
     `(~(reverse t) ~ts)
     (triplet (conj t (first ts)) (rest ts) (inc c)))))

(defn norm [s]
  (if (or (number? s) (= (class s) clojure.lang.Symbol))
    s
    (if (list? s)
      (if (<= (count s) 3)
        (reverse (map norm s))
        (let [tri       (triplet s)
              tri-first (nth tri 0)
              tri-rest  (nth tri 1)]
         (norm (conj (conj tri-rest tri-first) (first tri-first)))))
      (println "Error: expect input to be a lisp expression, i.e., a list."))))

(defn to-forth [s]
  (flatten (norm s)))

