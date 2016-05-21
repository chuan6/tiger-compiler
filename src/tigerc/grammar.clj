(ns grammar)

(def empty-string :ε)

(def slr
  {:terminals
   #{:array :break :do :else :end :for :function :if :in
     :let :nil :of :then :to :type :var :while
     :id :digits :string :ty-id ;:comment is omitted
     :comma :colon :semi-colon :open-paren :close-paren
     :open-bracket :close-bracket :open-brace :close-brace
     :period :assign :pipe :and
     :equal :gt :lt :diamond :leq :geq
     :minus :plus :star :slash empty-string}
   
   :start :expr

   :productions
   {:expr       [[:val]
                 [:lvalue :assign :expr]
                 [:open-paren :close-paren]
                 [:ty-id :open-brace :close-brace]
                 [:ty-id :open-brace :field-list :close-brace]
                 [:ty-id :open-bracket :expr :close-bracket :of :expr]
                 [:if :expr :then :expr :if-tail]
                 [:while :expr :do :expr]
                 [:for :id :assign :expr :to :expr :do :expr]
                 [:break]
                 [:let :decl-list :in :end]
                 [:let :decl-list :in :expr-seq :end]]
    :if-tail    [[empty-string]
                 [:else :expr]]
    :lvalue     [[:id]
                 [:lvalue :period :id]
                 [:lvalue :open-bracket :expr :close-bracket]]
    :expr-list  [[:expr]
                 [:expr-list :comma :expr]]
    :expr-seq   [[:expr]
                 [:expr-seq :semi-colon :expr]]
    :val        [[:minus :arith]
                 [:arith]]
    :arith      [[:arith :pipe :or-term]
                 [:or-term]]
    :or-term    [[:or-term :and :and-term]
                 [:and-term]]
    :and-term   [[:cmp-term :cmp :cmp-term]
                 [:cmp-term]]
    :cmp-term   [[:string]
                 [:cmp-term :cal-0 :term]
                 [:term]]
    :term       [[:term :cal-1 :factor]
                 [:factor]]
    :factor     [[:digits]
                 [:nil]
                 [:lvalue]
                 [:open-paren :expr-seq :close-paren]
                 [:id :open-paren :close-paren]
                 [:id :open-paren :expr-list :close-paren]]
    :cmp        [[:equal] [:lt] [:gt] [:leq] [:geq] [:diamond]]
    :cal-0      [[:plus] [:minus]]
    :cal-1      [[:star] [:slash]]
    :field-list [[:id :equal :expr]
                 [:field-list :comma :id :equal :expr]]
    :decl-list  [[:decl]
                 [:decl-list :decl]]
    :decl       [[:ty-decl]
                 [:var-decl]
                 [:fn-decl]]
    :ty-decl    [[:type :ty-id :equal :ty]]
    :ty         [[:ty-id]
                 [:open-brace :close-brace]
                 [:open-brace :ty-fields :close-brace]
                 [:array :of :ty-id]]
    :ty-fields  [[:ty-field]
                 [:ty-fields :comma :ty-field]]
    :ty-field   [[:id :colon :ty-id]]
    :var-decl   [[:var :id :assign :expr]
                 [:var :id :ty-id :assign :expr]]
    :fn-decl    [[:function :id :open-paren :close-paren :equal :expr]
                 [:function :id :open-paren :ty-fields :close-paren :equal :expr]
                 [:function :id :open-paren :close-paren :colon :ty-id :equal :expr]
                 [:function :id :open-paren :ty-fields :close-paren :colon :ty-id :equal :expr]]
    }})
