Parameter methNames : Set.

Inductive arithOperation : Set :=
              | add : arithOperation
              | substr:arithOperation
              | div : arithOperation
              | rem: arithOperation
              | mult: arithOperation.

Inductive expression : Set :=
              | var : expression
              | assign : expression -> expression -> expression
              | methInv: methNames -> expression->expression 
              | arithOp : arithOperation -> expression -> expression -> expression.

Inductive stmt : Set :=
              | exp: expression -> stmt
              | comp : stmt -> stmt -> stmt 
              | try_finally: stmt -> stmt -> stmt
              | try_catch : stmt -> stmt -> stmt.

Inductive relation : Set :=
              | lt : relation
              | le : relation
              | eq : relation 
              | ge : relation
              | gt: relation.

Inductive formula : Set := 
              | conj : formula -> formula -> formula
              | disj :  formula -> formula -> formula
              | _forall : expression ->  formula -> formula 
              | _exists : expression ->  formula -> formula
              |atomic : relation -> expression  -> expression -> formula.
              


Inductive wp_src : Set :=
             | wp_assign : expression -> predicate -> predicate


