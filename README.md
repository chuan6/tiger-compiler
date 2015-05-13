The Tiger Compiler (front-end)

...including a simple LR parser.

Notable features:

- on tokenzier (tigerc/tokenizer.clj):
  - nested comment;
  - complete id-to-tyid conversion;

- on grammar (tigerc/grammar.clj):
  - usage of empty-string (solving dangling-else problem);
  - non-left associative comparison operators;
  - suitable for simple LR parser (refer to the Dragon book);

- on context-free grammar processing (cfg.clj):
  - grammar structure validation (useful when a terminal is misspelled);
  - FIRST, and FOLLOW (both can work on grammar with left recursion);
  - construction of canonical collection from given grammar;
  - query on canonical collection, item-by-state, or state-by-item;
  - construction of action table, and goto table from given canonical
    collection;
  - generation of simple LR parser that incorperates customizable parse
    tree transformation function, for a suitable grammar;

- on parse tree to AST transformation (tigerc/ast.clj):
  - complete parse tree to AST transformation, to be called by parser;

- on semantic analysis (tigerc/semantics.clj, type.clj):
  - optimal disjoint-set data structure that manages equivalence between all
    types;
  - recursive function declaration within consecutive function declarations;
  - recursive type declaration within consecutive type declarations;
  - fully functional type aliasing, including detection of recursive type
    definition cycles that don't pass through a record or array type;
  - complete type checking for all expressions, except for :break;
  - un-assignable for-loop index variable.
