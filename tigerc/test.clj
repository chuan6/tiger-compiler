(ns tigerc.test)

(defmacro assert= [expected-form actual-form]
  (let [actual-form# (pr-str actual-form)]
    `(let [expected# ~expected-form
           actual# ~actual-form]
      (if (= expected# actual#)
        true
        (println "assert=:"
                 "expect" ~actual-form#
                 "to be evaluated to" expected#
                 "instead of" actual#)))))
