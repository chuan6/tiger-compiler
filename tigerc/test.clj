(ns tigerc.test)

(defmacro assert= [expected-form actual-form]
  (let [actual-form-str (pr-str actual-form)]
    `(let [expected# ~expected-form
           actual# ~actual-form]
      (if (= expected# actual#)
        true
        (println "assert=:"
                 "expect" ~actual-form-str
                 "to be evaluated to" expected#
                 "instead of" actual#)))))

(defmacro comprehend-tests
  ([] nil)
  ([tests & more-tests]
   `(when-not (empty? (concat (remove boolean ~tests)
                              (comprehend-tests ~@more-tests)))
      (throw (Exception.)))))
