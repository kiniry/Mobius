Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Open Scope Z_scope.

Definition var := Z.

Definition eq_var x y := Zeq_bool x y.

Definition num := Z.

Definition value := num.

Definition state : Set := var -> value.

Definition update (s:state) (x:var) (v:value) :=
 fun y => if eq_var x y then v else s y.



(* Definition of expression *)

Inductive unop: Set :=
 | Onot  : unop.

Inductive binop: Set :=
 | Oadd  : binop
 | Osub  : binop
 | Omul  : binop
 | Odiv  : binop
 | Oand  : binop
 | Oor   : binop
 | Ole   : binop
 | Oeq   : binop.

Inductive expr : Set :=
 | Econst : num -> expr
 | Evar   : var -> expr
 | EbinOp : binop -> expr -> expr -> expr
 | EunOp  : unop -> expr -> expr.



(* Semantique of expression *)

Definition bool_of_val (v:value) := negb (Zeq_bool v 0).

Definition val_of_bool (b:bool) := if b then 1 else 0. 

Definition eval_unop op v1 :=
 match op with
 | Onot => val_of_bool (negb (bool_of_val v1))
 end.

Definition eval_binop op v1 v2 := 
 match op with
 | Oadd  => v1 + v2 
 | Osub  => v1 - v2
 | Omul  => v1 * v2
 | Odiv  => v1 / v2
 | Oand  => val_of_bool (andb (bool_of_val v1) (bool_of_val v2))
 | Oor   => val_of_bool (orb (bool_of_val v1) (bool_of_val v2))
 | Ole   => val_of_bool (Zle_bool v1 v2)
 | Oeq   => val_of_bool (Zeq_bool v1 v2)
 end.

Fixpoint eval_expr (s:state) (e:expr) {struct e} : value :=
 match e with
 | Econst n        => n
 | Evar x          => s x  
 | EbinOp op e1 e2 => eval_binop op (eval_expr s e1) (eval_expr s e2)
 | EunOp  op e1    => eval_unop  op (eval_expr s e1)
 end.


