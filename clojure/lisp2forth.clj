(ns forth)

;; e.g., from (* (+ 1 2) 3 4) to (4 (3 (2 1 +) *) *)
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

;; take the current stack, and reduce it with the next symbol
(defn forth-reducer [stack next-symbol]
  (if (contains? #{'+ '- '* '/} next-symbol)
    (let [stack'    (pop  stack)
          arg1      (peek stack)
          arg2      (peek stack')
          unchanged (pop  stack')]
      (conj unchanged (eval `(~next-symbol ~arg1 ~arg2))))
    (conj stack next-symbol)))

;;return result of a forth calculation expression
(defn forth-calculator [s]
  (let [init-stack ()]
    (reduce forth-reducer init-stack s)))
