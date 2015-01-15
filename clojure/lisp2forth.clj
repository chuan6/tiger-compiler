(ns forth
  (require [clojure.edn :as edn]))

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

(defn lisp-to-forth [s]
  (eval-forth (to-forth s)))

(defn execute-symbol
  "Use `symbol` to perform an operation. Returns a vector
  of the new input and stack, intended to be applied to `eval-forth`."
  [symbol input stack]
  (let [a (first stack)
        b (second stack)
        nu-stack (rest (rest stack))
        nu-input (rest input)]
    (case symbol
      + [nu-input (cons (+ a b) nu-stack)]
      - [nu-input (cons (- a b) nu-stack)]
      * [nu-input (cons (* a b) nu-stack)])))

(defn eval-forth
  ([input] (eval-forth input []))
  ([input stack]
   ;; When the input is done the answer is TOS
   (if (empty? input)
     stack
     ;; Otherwise, read the first symbol...
     (let [first-symbol (first input)]
       (if (= (class first-symbol) clojure.lang.Symbol)
         ;; Execute symbols
         (apply eval-forth (execute-symbol first-symbol input stack))
         ;; Push everything else, hoping they're numerics.
         (eval-forth (rest input) (cons first-symbol stack)))))))
