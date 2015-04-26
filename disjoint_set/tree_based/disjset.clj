(ns disjoint-set)

(defn make-set [x] (ref {:rank 0 :path () :item x}))

(defn link [ex ey]
  (let [{r :rank p :path} @ex
        {s :rank q :path} @ey]
    (if (< r s)
      (dosync (alter ex assoc :path (conj q ey))
              ey)
      (dosync (alter ey assoc :path (conj p ex))
              (if (= r s) (alter ex assoc :rank (inc r)))
              ex))))

(defn find-set [ex]
  (let [path (:path @ex)]
    (if (empty? path)
      ex
      (let [root (find-set (first path))]
        (dosync (alter ex assoc :path `(~root))
                root)))))

(defn union [ex ey]
  (link (find-set ex) (find-set ey)))

(defn parent [ex]
  (let [path (:path @ex)]
    (if (empty? path) ex (first path))))

(defn test-0 []
  (let [a (make-set "hello")
        b (make-set "world")
        c (make-set "chuan")
        d (make-set "leo")
        e (make-set "compiler")
        f (make-set "tiger")]
    (assert (and (= (parent a) a)
                 (= (parent b) b)
                 (= (parent c) c)
                 (= (parent d) d)
                 (= (parent e) e)
                 (= (parent f) f)))
    (let [x (union a b)
          y (union c d)
          z (union e f)]
      (assert (and (= (:rank @x) (:rank @y) (:rank @z) 1)
                   (= x a)
                   (= y c)
                   (= z e)))
      (let [u (union b d)]
        (assert (and (= (:rank @u) 2) (= u a)))
        (let [v (union b f)]
          (assert (and (= (:rank @v) 2) (= u a)))
          (assert (= (find-set a)
                     (find-set b)
                     (find-set c)
                     (find-set d)
                     (find-set e)
                     (find-set f)
                     a))
          (println "test-0 passed."))))))
