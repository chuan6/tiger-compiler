(ns c)

;;; ONLY deal with expression that evaluates to an integer.
;;; Thus no expression other than a direct reference to a function can appear as the
;;; first element of a list.

;;; As a practice in syntax transformation, the following operations are done:

;;; (def symbol expr) is transformed into "int symbol = expr';", where expr' is
;;; the transformed form of expr.

;;; (defn symbol [symbol_1 symbol_2 ...] expr) is transformed into three parts:
;;; 1 int func_'generated' ();
;;;   - the declaration of a generated function name;
;;; 2 int (* const symbol)(int, int, ...) = func_'generated'
;;;   - the initialization of the given symbol as a const function point that points to
;;;     the generated function;
;;; 3 int func_'generated'(int symbol_1, int symbol_2, ...) {return expr';}
;;;   - the definition for the generated function name.

;;; (arith-op expr_1 expr_2 expr_3 ...) ->
;;; (...((expr_1' arith-op expr_2') arith-op expr_3') arith-op ...)
;;; where arith-op can be +, -, *, /.

;;; (compare-op expr_1 expr_2 expr_3 ...) ->
;;; (expr_1' compare-op expr_2') && (expr_2' compare-op' expr_3') && ...
;;; where compare-op can be >, <, =, >=, and <=. Note that compare-op' is of the same
;;; set of symbols as compare-op, except for "==", which corresponds to '='.

;;; (if expr_1 expr_2 expr_3) -> ((expr_1') ? expr_2' : expr_3')

;;; (let [symbol_1 expr_1 symbol_2 expr_2 ...] expr) is transformed into two parts:
;;; 1 int func_'generated' ();
;;;   - the declaration of a generated function name;
;;; 2 int func_'generated'(int symbol_1, int symbol_2, ...) {return expr';}
;;;   - the definition for the generated function name.
;;; and the original let expression becomes function call in C:
;;; (func_'generated' (expr_1' expr_2' ...)).

;;; Note that the map global-funcs gets updated when a new function is defined by
;;; defn expression.

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
  (let [[op e1 e2 & es] x]
    (if (nil? es)
      (map expr `(~e1 ~op ~e2))
      (norm-arith
       (-> es
           (conj `(~op ~e1 ~e2))
           (conj op))))))

;; (< 1 2) -> (1 < 2)
;; (< 1 2 3 4 5) -> ((1 < 2) && (2 < 3) && (3 < 4) && (4 < 5))
(defn norm-compare [x]
  (assert (>= (count x) 3))
  (let [[op e1 e2 & es] x]
    (if (nil? es)
      `(~(map expr `(~e1 ~op ~e2)))
      (-> (rest (rest x))
          (conj op)
          (norm-compare)
          (conj '&&)
          (conj (map expr `(~e1 ~op ~e2)))))))

;; (if (< 1 2) 1) -> ((1 < 2) ? 1 : 0)
(defn norm-if [x]
  (assert (let [n (count x)] (or (= n 3) (= n 4))))
  (let [[op c e1 e2] x]
    `(~(norm-compare c) \?
      ~(expr e1) \:
      ~(if (nil? e2) 0 (expr e2))))) ;0 is false value in C, as nil in Clojure

;; (def x 1) -> (const int x = (1) ;)
(defn norm-def [x]
  (assert (= (count x) 3))
  `(~'int ~(nth x 1) ~'= ~(expr (nth x 2)) \;))

(declare arglist)

(declare global-funcs)

(defn add-global-func [k v]
  (def global-funcs (assoc global-funcs k v)))

;; (arg1 arg2 arg) -> (arg1 , arg2 , arg3)
(defn add-comma [x]
  (if (empty? x)
    ()
    (loop [n (count x)
           y ()
           z x]
      (if (= n 1)
        (reverse (conj y (first z)))
        (recur (- n 1)
               (conj y (first z) \,)
               (rest z))))))

;; (defn factorial [n] (if (< n 2) 1 (* n (factorial (- n 1))))) ->
;; (
;;   (int func_7865 (int n) ; )
;;   (int (* const factorial) (int) = func ;)
;;   (int func_7865 (int n) { return (n < 2) ? 1 : (n * (* factorial) (n - 1)) ; })
;; )
(defn norm-defn [x]
  (assert (= (count x) 4))
  (let [[_ name argv body] x
        func (str "func_" (rand-int 2147483647))
        args (arglist argv)
        narg (count argv)
        argt (add-comma (repeat narg 'int))
        decl `(~'int ~func ~args \;)
        init `(~'int (\* ~'const ~name) ~argt \= ~func \;)]
    (add-global-func name
                     (fn [x]
                       ;;(name arg1 ... argn) -> ((* name) (arg1, ..., argn))
                       (assert (= (count x) (+ narg 1)))
                       `((\* ~name) ~(add-comma (map expr (rest x))))))
    (let [defi `(~'int ~func ~args \{ ~'return ~(expr body) \; \})]
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
   '/    norm-arith
   '<    norm-compare
   '>    norm-compare
   '=    norm-compare
   '<=   norm-compare
   '>=   norm-compare
   'if   norm-if
   'let  norm-let
   'def  norm-def
   'defn norm-defn
   })

(defn expr-helper [x]
  (if (or (number? x) (= clojure.lang.Symbol (class x)))
    (if (= x '=) `(~'==) `(~x))
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

;; [x y z] -> (int x , int y , int z)
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

