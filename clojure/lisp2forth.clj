(ns forth)

;; split a list into two parts, the first triplet of the list, and the rest.
;; e.g., from (+ 1 2 3 4 5 6 7) to ((+ 1 2) (3 4 5 6 7))
(defn first-triplet
  ([ts] (first-triplet () ts 0))
  ([t ts count]
   (if (= count 3)
     `(~(reverse t) ~ts)
     (first-triplet (conj t (first ts))
                    (rest ts)
                    (inc count)))))

;; e.g., from (* (+ 1 2) 3 4) to (4 (3 (2 1 +) *) *)
(defn norm [s]
  (if (or (number? s) (= (class s) clojure.lang.Symbol))
    s
    (if (list? s)
      (if (<= (count s) 3) ;TODO inefficiency: need to go through list everytime
        (reverse (map norm s))
        (let [[tri tri-rest] (first-triplet s)]
          (norm (-> tri-rest
                    (conj tri)
                    (conj (first tri))))))
      (println "Error: expect input to be a lisp expression, i.e., a list."))))

(defn to-forth [s]
  (flatten (norm s)))

