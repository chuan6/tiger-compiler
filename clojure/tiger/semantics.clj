(ns semantics
  (:require [grammar :as gmr]))

(def func-dict
  {:assign
   (fn [lval expr])

   :call
   (fn
     ([fn-name])
     ([fn-name argv]))

   :empty
   (fn [])

   :create-tmp
   (fn
     ([ty-name])
     ([ty-name fieldv])
     ([ty-name len init-val]))

   :if
   (fn
     ([pred expr])
     ([pred expr expr']))

   :while
   (fn [pred expr])

   :for
   (fn [i-name low high expr])

   :break
   (fn [])

   :let
   (fn
     ([declv])
     ([declv exprs]))

   :lvalue
   (fn [type & argv])

   :exprs
   (fn [exprv])

   :neg
   (fn [x])

   :or
   (fn [x y])

   :and
   (fn [x y])

   :cmp
   (fn [type x y])

   :string
   (fn [s])

   :cal
   (fn [type x y])

   :int
   (fn [c])

   :nil
   (fn [])

   :assign-fields
   (fn [pairv])

   :consec-ty-decl
   (fn [declv])

   :consec-fn-decl
   (fn [declv])

   :ty-decl
   (fn [ty-name ty])

   :create-ty
   (fn [type x])

   :ty-assoc
   (fn [v-name ty-name])

   :var-decl
   (fn
     ([v-name expr])
     ([v-name ty-name expr]))

   :fn-decl
   (fn [void? fn-name & v])
   })
