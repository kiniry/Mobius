Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Open Scope Z_scope.
Inductive Var : Set := 
Name : Z -> Z -> Var.
Definition vareq := fun (v1 v2: Var) => 
match v1 with 
| Name z1 z2 => match v2 with 
                             | Name z3 z4 => andb (Zeq_bool z1 z3) (Zeq_bool z2 z4) 
                             end
end.
Definition Num := Z.
Definition Value := Num.
Inductive BinOp: Set :=
| add : BinOp
| sub: BinOp
| mul : BinOp
| div : BinOp
| bAnd : BinOp
| bOr : BinOp
| eqle :  BinOp
| eq: BinOp.
Inductive UnOp: Set :=
| bNot : UnOp.
Infix "<=" := eqle: W_Scope.
Infix "=" := eq: W_Scope.
Infix "+" := add: W_Scope.
Infix "-" := sub: W_Scope.
Infix "*" := mul: W_Scope.
Infix "/" := div: W_Scope.
Infix "&&" := bAnd: W_Scope.
Infix "||" := bOr: W_Scope.
Infix "!" := bNot (at level 30) : W_Scope .

Inductive NumExpr : Set :=
| nval : Num -> NumExpr
| nvar : Var -> NumExpr
| binOpExpr: BinOp -> NumExpr -> NumExpr -> NumExpr
| unOpExpr: UnOp -> NumExpr -> NumExpr.



(* Variable v: Var.
Check ((v <- (nval 1)); Skip). *)

Definition State:  Set := Var -> Num.
Definition EmptyState : State := 
fun (v : Var) => 0.


Definition update : State -> Var -> Num -> State :=
fun (s : State) (v : Var) (val : Num) =>
       fun (v1: Var) => if (vareq v v1) then val else (s v1).
Definition Num2Bool : Num -> bool :=
fun (n : Num) => (negb (Zeq_bool  n 0)).

Fixpoint neval (s: State) (n: NumExpr) {struct n} : Num :=
     match n with 
     | nval a => a
     | nvar v => (s v) 
     | binOpExpr o a1 a2 => match o with 
                                          | add => Zplus (neval s a1)  (neval s a2)
                                          | sub =>  (neval s a1) - (neval s a2)
                                          | mul =>  Zmult (neval s a1)  (neval s a2)
                                          | div =>  Zdiv (neval s a1)  (neval s a2)
                                          | bAnd => if (andb (Num2Bool (neval s a1))
                                                                          (Num2Bool (neval s a2))) then 1 else 0
                                          | bOr => if (orb (Num2Bool (neval s a1))
                                                                    (Num2Bool (neval s a2))) then 1 else 0                                          
                                          | eq => if (Zeq_bool (neval s a1)(neval s a2) ) then 1 else 0
                                          | eqle => if (Zle_bool (neval s a1) (neval s a2)) then 1 else 0
                                          end
     | unOpExpr o a => match o with 
                                      | bNot => if (Zeq_bool (neval s a) 0) then 1 else 0
                                      end
     end.
(*****************************************************************)
(* Assertion language*)
Definition Assertion := State -> Prop .

Definition update_assert : Assertion -> Var -> NumExpr ->  Assertion := 
fun (a: Assertion) (v: Var) (val : NumExpr) =>
           fun (s: State) => a (update s v (neval s val)) .

Definition EmptyAssertion := 
fun (s: State) => True.
(*Definition if_assert : NumExpr -> AssertionWP -> AssertionWP -> AssertionWP := 
fun (b: NumExpr) (a1 : AssertionWP) (a2: AssertionWP) =>
          fun (s: State) => ((assert_eval s b) -> a1 s) /\ ((not (assert_eval s b)) -> a2 s). *)

(* Fixpoint  quant  (s: State )(l: list Var)(p: Prop) {struct l} : Prop :=
match l with
| nil => p
| x :: l1  =>  (quant  s l1  ( forall v ,  (s x)  = v  ->  p ) )
end. 
*)
(* Definition assert_forall: list Var -> Assertion  -> Assertion := 
fun (l : list Var) (assert : Assertion)  =>
          fun (s: State) => ( quant s l ( assert s)) . *)

Definition assert_conj : Assertion-> Assertion  -> Assertion := 
fun (ass1: Assertion) (ass2 : Assertion)  =>
          fun (s: State) => (ass1 s) /\ (ass2 s).



Variable assert_Prop_in_State: State -> Prop -> Prop.

(* Definition assert_implies : Prop -> Assertion  -> Assertion := 
  fun (cond : Prop) (assert : AssertionWP)  =>
          fun (s: State) =>  ( assert_Prop s cond ) -> assert s . *)

(* for a given list of modified variables during a loop returns the correctness condition for this statement, i.e. *) 
(* a predicate that confirms that nothing else has been modified and also that the invariant holds *)
Definition invAndmodifiesCorrect : Assertion -> list Var -> Assertion := 
     fun ( inv: Assertion)( l: list Var) => 
         fun (st_init: State) =>  
          ( forall st_fin : State, forall  x: Var,   not (In x  l)  -> ( st_fin x ) = ( st_init x ) ) /\  (inv st_init) .   

Inductive Invariant : Prop := 
| invMod : Assertion ->   list Var-> Invariant 
| invWithoutMod : Assertion -> Invariant.
(* end Assert Language *)
(*****************************************************************)
Section STMT.
Variable Invariant : Type.
Inductive Stmt  : Type :=
| Skip: Stmt
| Affect : Var -> NumExpr -> Stmt
| If : NumExpr -> Stmt -> Stmt -> Stmt
| While : NumExpr -> Invariant  -> Stmt -> Stmt
| Seq: Stmt -> Stmt -> Stmt.
End STMT.
(* ************** LES INVARIANT C EST ICI ** *)
Inductive Invariant_m : Type := 
inv_m : Assertion ->   list Var-> Invariant_m.
Inductive Invariant_j : Type :=
inv_j : Assertion -> Invariant_j.

Definition stmt_m := Stmt Invariant_m.
Definition stmt_j := Stmt Invariant_j.
(*Inductive Stmt : Set :=
| Skip: Stmt
| Affect : Var -> NumExpr -> Stmt
| If : NumExpr -> Stmt -> Stmt -> Stmt
| While : Invariant -> NumExpr -> Stmt -> Stmt
| Seq: Stmt -> Stmt -> Stmt.*)
Notation "v <- val |> a" := (Affect a v val) (at level 30).
Notation "b ; c |> a" := (Seq a b c) (at level 30).

Section semantique.
Variable inv: Type.
Inductive execBs : State -> Stmt inv   -> State -> Prop :=
| execBsSkip : forall s, execBs s (Skip inv) s
| execBsAffect: forall s v exp  ,   execBs s (Affect inv v exp) (update s v (neval s exp))
| exectBsIfTrue: forall s s' b stThen stElse, 
        neval s b <> 0 -> execBs s stThen s'  ->
                       execBs s (If inv b stThen stElse) s'
| exectBsIfFalse: forall s s' b stThen stElse, 
        neval s b = 0 -> execBs s stElse s'  ->
                       execBs s (If inv b stThen stElse) s'
| execBsWhileFalse: forall b i st s, neval s b = 0 -> execBs s ((While inv) b i  st) s
| execBsWhileTrue: forall b i st s s' s'', neval s b <> 0 -> 
                                      (execBs s st s') -> (execBs s' (While inv b i  st) s'') ->
                                      (execBs s (While inv b i st) s'')
| execBsSeq: forall s s' s'' st1 st2, execBs s st1 s' -> execBs s' st2 s'' -> execBs s (Seq inv st1 st2) s''.


(*
Inductive execSs : Stmt inv -> State -> option (Stmt inv) -> State -> Prop :=
| execSsAffect : forall s v exp, execSs (Affect inv v exp) s  None (update s v (neval s exp))
| execSsIfTrue: forall b stThen stElse s, neval s b <> 0  -> execSs  (If inv b stThen stElse) s (Some stThen) s
| execSsIfFalse: forall b stThen stElse s,  neval s b = 0 -> execSs  (If inv b stThen stElse) s (Some stElse) s
| execSsWhileFalse: forall i b st s, neval s b = 0  -> execSs (While inv b i st) s None s
| execSsWhileTrue: forall i b st s, neval s b <> 0  -> execSs (While inv b i st) s (Some (Seq inv st (While inv b i st))) s
| execSsSeq1: forall st1 st1' st2 s s',  execSs st1 s (Some st1') s' -> execSs (Seq inv st1 st2) s  (Some (Seq inv st1' st2)) s'
| execSsSeq2: forall st1  st2 s s',  execSs st1 s None s' -> execSs (Seq inv st1 st2) s  (Some st2) s'
| execSsSkip: forall s, execSs (Skip inv) s None s.

Hint Immediate execSsSkip.

Inductive execSsStar :  Stmt inv -> State -> option (Stmt inv) -> State -> Prop :=
| execSsSt : forall s st s' st' s'', execSs st s (Some st') s' -> execSsStar st' s' None s'' -> execSsStar st s None s''
| execSsStNone : forall s st s' , execSs st s None s'  -> execSsStar st s None s'.
Axiom triche: forall p: Prop, p.
*)
End semantique.

