(ns forth)

;;;Usage example: (to-forth '(* (+ 1 2) 3 4))

;;e.g., from (* (+ 1 2) 3 4) to (4 (3 (2 1 +) *) *)
(defn norm [s]
  (if (or (number? s) (= (class s) clojure.lang.Symbol))
    s
    (if (seq? s)
      (if (<= (count s) 3)
        (reverse (map norm s))
        (let [[op a b & more] s]
          (norm (conj more `(~op ~a ~b) op))))
      (println "Error: expect input to be a lisp expression, i.e., a list." (type s)))))

(defn to-forth [s]
  (flatten (norm s)))

;;Take the current stack, and reduce it with the next symbol.
(defn forth-reducer [stack next-symbol]
  (if (contains? #{'+ '- '* '/} next-symbol)
    (let [stack'    (pop  stack)
          arg1      (peek stack)
          arg2      (peek stack')
          unchanged (pop  stack')]
      (conj unchanged (eval `(~next-symbol ~arg1 ~arg2))))
    (conj stack next-symbol)))

;;Return result of a forth calculation expression.
(defn forth-calculator [s]
  (let [init-stack ()]
    (peek (reduce forth-reducer init-stack s))))

(defn myrand [upper]
  (+ (rand-int (dec upper)) 1)) ;plus 1 to avoid divid-by-zero

(defn gen-test-op []
  (let [opvec ['+ '- '* '/]
        n     (count opvec)]
    (nth opvec (myrand n))))

(defn gen-test-cell [max]
  (assert (>= max 2))
  (if (= max 2)
    `(~(gen-test-op) ~(myrand 100) ~(myrand 100))
    (loop [c     max
           built `(~(gen-test-op))]
      (if (= c 0)
        (reverse built)
        (recur (- c 1) (conj built (gen-test-cell (- max 1))))))))

(defn gen-test []
  (let [acase   (gen-test-cell 4) ;Note: 4 here is large enough
        clojure (eval acase)
        forth   (forth-calculator (to-forth acase))]
    (println clojure "; clojure result")
    (println forth "; forth result")
    (= clojure forth)))

(defn test [n]
  (assert (>= n 0))
  (loop [success? true
         nmore    n
         m        0]
    (if (= nmore 0)
      (do (println n "test cases run;" m "failed.")
          success?)
      (let [result (gen-test)]
        (recur (and result success?)
               (dec nmore)
               (if result m (inc m)))))))
