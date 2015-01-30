(ns c)

(defn print-items [s]
  (if (empty? s)
    (println)
    (do (apply println (first s))
        (print-items (rest s)))))

(defn print-c [c]
    (print-items (:func-decl c))
    (print-items (:funcptr-init c))
    (print-items (:var-init c))
    (print-items (:func-def c)))

(declare expr-expr)

(defn global
  ([clj]
   (global clj
           {:var-init ()     ; e.g. int x = 0;
            :func-decl ()    ; e.g. int f(int);
            :funcptr-init () ; e.g. int (*fp)(int) = f;
            :func-def ()}))  ; e.g. int f(int x) {return (x < 2)? 1:(x * (*fp)(x-1));}
  ([clj c]
   (if (empty? clj)
     (print-c (let [var-inits (:var-init c)
                    func-decls (:func-decl c)
                    funcptr-inits (:funcptr-init c)
                    func-defs (:func-def c)]
                (-> c
                    (assoc :var-init (reverse var-inits))
                    (assoc :func-decl (reverse func-decls))
                    (assoc :funcptr-init (reverse funcptr-inits))
                    (assoc :func-def (reverse func-defs)))))
     (global
      (rest clj)
      (let [result (expr-expr (first clj))] ; globals have meta data from expr-expr
        (loop [ks (keys result)
               m c]
          (if (empty? ks)
            m
            (recur (rest ks)
                   (let [k (first ks)
                         stmts (get m k)
                         s (get result k)]
                     (assoc m k (conj stmts s)))))))))))

(defn test-case []
  (global
   '((def x 1)
     (def y 2)
     (defn f1 [] (if (< x y 3 4) 1 0))
     (defn factorial [n] (if (< n 2) 1 (* n (factorial (- n 1)))))
     (defn fx [] (let [a 1 b 2 c 3] (+ a b c))))))

(declare pre-to-infix)
(declare expr)

;; (+ 1 2 3 (- 5 4)) -> (((1 + 2) + 3) + (5 - 4))
(defn norm-arith [x]
  (assert (>= (count x) 3))
  (if (= (count x) 3)
    (pre-to-infix (map expr x))
    (let [[op a b & more] x]
      (norm-arith (conj more `(~op ~a ~b) op)))))

;; (< 1 2) -> (1 < 2)
;; (< 1 2 3 4 5) -> ((1 < 2) && (2 < 3) && (3 < 4) && (4 < 5))
(defn norm-compare [x]
  (assert (>= (count x) 3))
  (if (= (count x) 3)
    `(~(pre-to-infix (map expr x)))
    (let [[op a b & more] x]
      (conj (norm-compare (conj (rest (rest x)) (first x)))
            '&& `(~a ~op ~b)))))

;; (if (< 1 2) 1) -> ((1 < 2) ? 1 : 0)
(defn norm-cond [x]
  (let [n (count x)
        c (nth x 1)]
    (assert (or (= n 3) (= n 4)))
    (case n
      3 `(~(norm-compare c) \? ~(expr (nth x 2)) \: 0)
      4 `(~(norm-compare c) \? ~(expr (nth x 2)) \: ~(expr (nth x 3))))))

;; (def x 1) -> (const int x = (1) ;)
(defn norm-def [x]
  (assert (= (count x) 3))
  `(~'int ~(nth x 1) ~'= ~(expr (nth x 2)) \;))

(declare arglist)

(defn argtypelist [n]
  (assert (>= n 0))
  (if (= n 0)
    ()
    (loop [c n
           x ()]
      (if (= c 1)
        (conj x 'int) ; no need to reverse here
        (recur (- c 1) (conj x 'int \,))))))

(declare global-funcs)

(defn add-global-func [k v]
  (def global-funcs (assoc global-funcs k v)))

;; (arg1 arg2 arg) -> (arg1 , arg2 , arg3)
(defn add-comma [x]
  (loop [n (count x)
         y ()
         z x]
    (if (= n 1)
      (reverse (conj y (first z)))
      (recur (- n 1) (conj y (first z) \,) (rest z)))))

;; (defn factorial [n] (if (< n 2) 1 (* n (factorial (- n 1))))) ->
;; (
;;   (int func_7865 (int n) ; )
;;   (int (* const factorial) (int) = func ;)
;;   (int func_7865 (int n) { return (n < 2) ? 1 : (n * (* factorial) (n - 1)) ; })
;; )
(defn norm-defn [x]
  (assert (= (count x) 4))
  (let [func (str "func_" (rand-int 2147483647))
        name (nth x 1)
        argv (arglist (nth x 2))
        narg (count (nth x 2))
        argt (argtypelist narg)
        body (nth x 3)
        decl `(~'int ~func ~argv \;)
        init `(~'int (\* ~'const ~name) ~argt \= ~func \;)]
    (add-global-func name
                     (fn [x] ; (name arg1 ... argn) -> ((* name) (arg1, ..., argn))
                       (assert (= (count x) (+ narg 1)))
                       `((\* ~name) ~(add-comma (map expr (rest x))))))
    (let [defi `(~'int ~func ~argv \{ ~'return ~(expr body) \; \})]
      `(~decl ~init ~defi))))

(defn take-helper [v start]
  (assert (vector? v))
  (let [n (count v)]
    (loop [i start
           r []]
      (if (>= i n)
        r
        (recur (+ i 2) (conj r (nth v i)))))))

(defn take-evenly-indexed [v] (take-helper v 0))
(defn take-oddly-indexed [v] (take-helper v 1))

;; (let [x 1 y 2] (+ x y)) ->
;; (int func_7866 (int x, int y) { return (x + y) ; })
;; (func_7866 (1 , 2))
(defn norm-let [x]
  (let [func (str "func_" (rand-int 2147483647))
        args (take-evenly-indexed (nth x 1))
        argv (arglist args)
        vals (take-oddly-indexed (nth x 1))
        body (nth x 2)]
    `((~'int ~func ~argv \;) ; function declaration
      (~'int ~func ~argv \{ ~'return ~(expr body) \; \}) ; function definition
      (~func ~(add-comma (list* (map expr vals)))) ; function call (returns value)
      )))

(def global-funcs ; will be updated by defn expressions
  {'+    norm-arith
   '-    norm-arith
   '*    norm-arith
   '<    norm-compare
   '>    norm-compare
   '=    norm-compare
   '<=   norm-compare
   '>=   norm-compare
   'if   norm-cond
   'let  norm-let
   'def  norm-def
   'defn norm-defn
   })

(defn expr-helper [x]
  (if (or (number? x) (= clojure.lang.Symbol (class x)))
    `(~x)
    (let [handler (get global-funcs (first x))
          norm (handler x)]
      (condp = handler ; add meta info for def, defn, and let
        norm-def  `(~norm
                    {:var-init ~norm})
        norm-defn `(~norm
                    {:func-decl ~(nth norm 0)
                     :funcptr-init ~(nth norm 1)
                     :func-def ~(nth norm 2)})
        norm-let  `(~(nth norm 2)
                    {:func-decl ~(nth norm 0)
                     :func-def ~(nth norm 1)})
        `(~norm)))))

(defn expr [x] (first (expr-helper x)))
(defn expr-expr [x] (second (expr-helper x)))

(defn arglist [v]
  (if (empty? v)
    ()
    (let [limit (- (count v) 1)]
      (loop [r '()
             i 0]
        (if (= i limit)
          (flatten (reverse (conj r `(~'int ~(v i)))))
          (recur (conj r `(~'int ~(v i) \,)) (+ 1 i)))))))

;; translate a triplet from prefix notation to infix
(defn pre-to-infix [x]
  (let [[op a b] x]
    `(~a ~op ~b)))

