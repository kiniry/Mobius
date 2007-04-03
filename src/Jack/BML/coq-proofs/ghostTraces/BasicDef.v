Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Open Scope Z_scope.
(*normal variables*)
(*Definition var := Z.*)

Variable methodNames : Set.

Variable  event :  Set.
(* program variables  *)
Definition var := Set.
Parameter var_dec: forall x y : var, {x = y} + {x <> y}.
Definition eq_var : var -> var -> bool :=   (fun x y => if (var_dec x y) then true else false).
(**************************)

(* ghost variables *)
Definition gVar := Set.
Parameter gVar_dec: forall x y : var, {x = y} + {x <> y}.
Definition eq_gVar : gVar -> gVar -> bool := (fun x y => if (var_dec x y) then true else false).
(**************************)
(*
Definition var := Z.
 
Definition eq_var x y := Zeq_bool x y.

(*ghost variables*)
Definition gVar := Z.

Definition eq_gVar x y := Zeq_bool x y.
*)

Definition value := Z.

Definition state : Type := var -> Z.

Definition gState : Type := gVar -> Z.
 
Definition update (s:state) (x:var) (v:value) :=
 fun y => if eq_var x y then v else s y.

Definition gUpdate(s: gState ) ( x: gVar) (v:value) := 
 fun y => if eq_var x y then v else s y.

(* Definition of expression *)

Inductive unop: Set :=
 | Onot  : unop.

Inductive binop: Set :=
 | Oadd  : binop
 | Osub  : binop
 | Omul  : binop
 | Odiv  :  binop
 | Oand  : binop
 | Oor   : binop
 | Ole   : binop
 | Oeq   : binop.

Inductive expr : Type :=
 | Econst : Z -> expr
 | Evar   : var -> expr
 | EbinOp : binop -> expr -> expr -> expr
 | EunOp  : unop -> expr -> expr.

Inductive gExpr : Type :=
 | gEconst : Z -> gExpr
 | gEvar   : var -> gExpr
 | gvar : gVar -> gExpr
 | gEbinOp : binop -> gExpr -> gExpr -> gExpr
 | gEunOp  : unop -> gExpr -> gExpr. 

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

(* Semantique of expression *)
Fixpoint eval_expr (s:state) (e:expr) {struct e} : value :=
 match e with
 | Econst n        => n
 | Evar x          => s x  
 | EbinOp op e1 e2 => eval_binop op (eval_expr s e1) (eval_expr s e2)
 | EunOp  op e1    => eval_unop  op (eval_expr s e1)
 end.

(* Semantique of expression *)
Fixpoint gEval_expr (s:state)(gs: gState) (e:gExpr) {struct e} : value :=
 match e with
 | gEconst n   => n
 | gEvar x       => s x  
 | gvar     x    => gs x 
 | gEbinOp op e1 e2 => eval_binop op (gEval_expr s gs e1) (gEval_expr s gs e2)
 | gEunOp  op e1    => eval_unop  op (gEval_expr s gs e1)
 end.
