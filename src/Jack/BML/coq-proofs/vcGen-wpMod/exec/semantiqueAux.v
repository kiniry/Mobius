Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Open Scope Z_scope.

Inductive Var : Set := 
 | Name : Z -> Z-> Var.

Definition vareq := fun (v1 v2: Var) => 
match v1 with 
| Name z1 z2 => match v2 with 
                             | Name z3 z4 => andb (Zeq_bool z1 z3) (Zeq_bool z2 z4) 
                             end
end.


Lemma varEqDec : forall v1 v2 : Var ,  {v1 = v2} + {v1 <> v2}.
decide equality.
apply Z_eq_dec.
apply Z_eq_dec.
Qed.


Inductive AuxVar : Set :=  
 | AuxName : Var-> Z-> AuxVar.


Definition varAuxEq := fun (v1 v2: AuxVar) => 
match v1 with 
| AuxName var1 z1 => match v2 with 
                             | AuxName var2 z2 => andb (vareq var1 var2 ) (Zeq_bool z1 z2) 
                             end
end.


Lemma varAuxEqDec : forall v1 v2 : AuxVar ,  {v1 = v2} + {v1 <> v2}.
decide equality.
apply Z_eq_dec.
apply varEqDec.
Qed.

(* Inductive AllVar : Set :=
 | progvar  : Var -> AllVar 
 | auxvar :  AuxVar -> AllVar. 
  
Definition varAllVarEq ( v1 v2 : AllVar ) : bool :=
 match v1  with
| progvar v1'  => match v2 with 
                             | progvar v2' => (vareq v1' v2')
			     | _ => false 
                             end
| auxvar v1' => match v2 with
			    | auxvar v2' =>  ( varAuxEq v1' v2')
		            | _ => false 
		            end
end.

Lemma varAllEqDec : forall v1 v2 : AllVar ,  {v1 = v2} + {v1 <> v2}.
decide equality.
apply  varEqDec.
apply varAuxEqDec.
Qed. *)
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
(*| nAuxVar : AuxVar -> NumExpr *)
| binOpExpr: BinOp -> NumExpr -> NumExpr -> NumExpr
| unOpExpr: UnOp -> NumExpr -> NumExpr.





(*change the state to be a function that maps aux var and  program var to values *)
Definition State:  Set := Var -> Num.
(* Definition EmptyState : State :=  fun (v : Var) => 0. *)
Definition AuxState : Set := AuxVar -> Num.

Definition update : State -> Var -> Num -> State :=
fun (s : State) (v : Var) (val : Num) =>
       fun (v1: Var) => if (vareq v v1) then val else (s v1).


Definition Num2Bool : Num -> bool :=
fun (n : Num) => (negb (Zeq_bool  n 0)).

Fixpoint neval (s: State) (sAux : AuxState) (n: NumExpr) {struct n} : Num :=
     match n with 
     | nval a => a
     | nvar v => (s   v  )
     (*| nAuxVar v => (sAux v ) *) 
     | binOpExpr o a1 a2 => match o with 
                                          | add => Zplus (neval s sAux a1)  (neval s sAux a2)
                                          | sub =>  (neval s sAux a1) - (neval s sAux a2)
                                          | mul =>  Zmult (neval s sAux a1)  (neval s  sAux a2)
                                          | div =>  Zdiv (neval s sAux a1)  (neval s sAux a2)
                                          | bAnd => if (andb (Num2Bool (neval s sAux a1))
                                                                          (Num2Bool (neval s sAux a2))) 
                                                                           then 1 
                                                                           else 0
                                          | bOr => if (orb (Num2Bool (neval s sAux a1))
                                                                    (Num2Bool (neval s sAux a2))) then 1 else 0                                          
                                          | eq => if (Zeq_bool (neval s sAux a1)(neval s sAux a2) ) 
                                                           then 1 
                                                           else 0
                                          | eqle => if (Zle_bool (neval s sAux a1) (neval s sAux a2)) 
                                                             then 1 
                                                             else 0
                                          end
     | unOpExpr o a => match o with 
                                      | bNot => if (Zeq_bool (neval s sAux a) 0) 
                                                          then 1 
                                                          else 0
                                      end
     end.
(*****************************************************************)
(* Assertion language*)
Inductive myProp : Set := 
| p_or : myProp -> myProp -> myProp
| p_and : myProp -> myProp -> myProp
| p_implies : myProp -> myProp -> myProp
| p_in : Var -> list Var  -> myProp
| p_eq : Num -> Num -> myProp
| p_neq : Num -> Num -> myProp
| p_not: myProp -> myProp
| p_true :  myProp
| p_false : myProp 
| p_forallsAux : ( AuxState  -> myProp) ->myProp 
|p_existsAux : ( AuxState  -> myProp) ->myProp
| p_foralls :  (State -> myProp) -> myProp
| p_exists : (State ->myProp) -> myProp
| p_forallv : (Var -> myProp) -> myProp.

Definition Assertion := ( State * AuxState) -> myProp .

(*NB : define a function that checks if  the index z is fres in the proposition P. *)
(*This means that in P should appear no auxiliary variable constructed with that index *)
Axiom  isFresh : Z -> Assertion -> Prop. 
(* to be defined : the definition for myProp must be changed before for the cases p_eq, p_neq *)
(* match p with
| p_or  P1 P2 => (isFresh var P1 ) /\ ( isFresh var P2)
| p_and P1 P2 => (isFresh var P1 ) /\ ( isFresh var P2)
| p_implies P1 P2 => (isFresh var P1 ) \/ ( isFresh var P2)
| p_in  v' P2 => not (varEqDec var v') /\  ( isFresh var P2)
| p_eq z1 z2  => True   *)

 


Definition update_assert : Assertion -> Var -> NumExpr ->  Assertion := 
fun (a: Assertion) (v: Var) (val : NumExpr) =>
           fun ( st : State*AuxState ) => let (s, sAux) := st in
                                     a (update s v (neval s sAux val) , sAux) .

Fixpoint evalMyProp (p: myProp) {struct p}: Prop :=
match p with 
| p_or p1 p2 => evalMyProp p1 \/  evalMyProp p2
| p_and p1 p2 => evalMyProp p1 /\  evalMyProp p2
| p_implies p1 p2 => evalMyProp p1 ->  evalMyProp p2
| p_in p1 p2 => In p1 p2
| p_eq p1 p2 => p1 = p2
| p_neq p1 p2 => p1 <> p2
| p_not p1  => not (evalMyProp p1)
| p_true => True
| p_false => False
| p_forallsAux p1 => forall stAux, (evalMyProp (p1 stAux) )
| p_existsAux p1 => exists stAux, (evalMyProp (p1 stAux) )
| p_foralls p1 => forall st, evalMyProp (p1 st)
| p_exists p1 => exists st, evalMyProp (p1 st)
| p_forallv p1 => forall var, evalMyProp (p1 var)
end.
Definition EmptyAssertion := 
fun (s: State) => p_true.
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
          fun (s: State*AuxState ) => p_and (ass1 s) (ass2 s).



Variable assert_Prop_in_State: State -> Prop -> Prop.

(* Definition assert_implies : Prop -> Assertion  -> Assertion := 
  fun (cond : Prop) (assert : AssertionWP)  =>
          fun (s: State) =>  ( assert_Prop s cond ) -> assert s . *)

(* for a given list of modified variables during a loop returns the correctness condition for this statement, i.e. *) 
(* a predicate that confirms that nothing else has been modified and also that the invariant holds *)
(* Definition invAndmodifiesCorrect : Assertion -> list Var -> Assertion := 
     fun ( inv: Assertion)( l: list Var) => 
         fun (st_init: State) =>  
          p_and ( forall st_fin : State, forall  x: Var,   p_implies (p_not (p_in x  l) ) (p_neq ( st_fin x )  ( st_init x )))   (inv st_init).   
*)
Inductive Invariant : Set := 
| invMod : Assertion ->   list Var-> Invariant 
| invWithoutMod : Assertion -> Invariant.
(* end Assert Language *)
(*****************************************************************)
Section STMT.
Variable Invariant : Set.
Inductive Stmt  : Set :=
| Skip: Stmt
| Affect : Var -> NumExpr -> Stmt
| If : NumExpr -> Stmt -> Stmt -> Stmt
| While : NumExpr -> Invariant  -> Stmt -> Stmt
| Seq: Stmt -> Stmt -> Stmt.


Inductive StmtIndexed  : Set :=
| SkipInd: Z -> StmtIndexed
| AffectInd : Z -> Var -> NumExpr -> StmtIndexed
| IfInd : Z -> NumExpr -> StmtIndexed -> StmtIndexed -> StmtIndexed
| WhileInd : Z -> NumExpr -> Invariant  -> StmtIndexed -> StmtIndexed
| SeqInd: Z  -> StmtIndexed -> StmtIndexed -> StmtIndexed.

End STMT.

Section indexingStmt.
Variable inv : Set.
Inductive setStmtId : (Z * Stmt inv )  -> ( Z * StmtIndexed inv )  -> Prop := 
  | setSkipInd : forall z,  ( setStmtId (z, (Skip inv) ) ( z +1 , (SkipInd inv z )))
  | setAffectInd : forall var val z,  ( setStmtId (z, Affect inv  var val  ) ( z +1 , (AffectInd inv z var val  )))
  | setIfInd  :  forall stmt1 stmt2  expB stmtInd1 stmtInd2 zT zF z ,
                      ( setStmtId ( (z + 1 , stmt1)  )( zT, stmtInd1 )) ->
                      ( setStmtId ( (zT, stmt2)  )( zF, stmtInd2 )) ->
	              ( setStmtId (z, If  inv expB stmt1 stmt2  ) ( zF , (IfInd inv z expB stmtInd1 stmtInd2  ))) 
  | setWhileInd : forall stmt invariant expB  stmtInd z zBody , 
		     ( setStmtId (z +1 , stmt ) ( zBody, stmtInd)) ->
	             ( setStmtId ( z, While inv  expB invariant  stmt )
                                         (zBody, WhileInd inv  z expB invariant  stmtInd  ))
  | setSeqInd : forall stmt1 stmt2  stmtInd1 stmtInd2  z z1 z2,
   	               ( setStmtId ( (z +1 , stmt1)  )( z1, stmtInd1 )) ->
                       ( setStmtId ( (z1, stmt2)  )( z2, stmtInd2 )) ->
                       ( setStmtId ( z, Seq inv stmt1 stmt2)( z2 , SeqInd inv z stmtInd1 stmtInd2 )).
End indexingStmt.





(* ************** LES INVARIANT C EST ICI ** *)
Inductive Invariant_m : Set := 
inv_m : Assertion ->   list Var-> Invariant_m.
Inductive Invariant_j : Set :=
inv_j : Assertion -> Invariant_j.

Definition stmt_m := StmtIndexed Invariant_m.
Definition stmt_j := StmtIndexed  Invariant_j.





Notation "v <- val |> a" := (Affect a v val) (at level 30).
Notation "b ; c |> a" := (Seq a b c) (at level 30).

Section semantique.
Variable inv: Set.
Inductive execBs : State -> StmtIndexed inv   -> State -> Set :=
| execBsSkip : forall s z, execBs s (SkipInd  inv z) s
| execBsAffect: forall s sAux v exp z,   execBs s
                                                             (AffectInd inv z v exp) 
                                                             ( (update s v (neval s sAux exp)) )
| exectBsIfTrue: forall s sAux s' b stThen stElse z , 
        neval s sAux b <> 0 -> execBs s stThen s'  ->
                       execBs s (IfInd inv z b stThen stElse) s'
| exectBsIfFalse: forall s sAux s' b stThen stElse z, 
        neval s sAux b = 0 -> execBs s stElse s'  ->
                       execBs s (IfInd inv z b stThen stElse) s'
| execBsWhileFalse: forall b i st s sAux z, neval s sAux b = 0 -> execBs s ((WhileInd inv) z b i  st) s
| execBsWhileTrue: forall b invariant st s sAux s' s'' z, neval s sAux b <> 0 -> 
                                      (execBs s st s') -> (execBs s' (WhileInd inv z b invariant  st) s'') ->
                                      (execBs s (WhileInd inv z b invariant st) s'')
| execBsSeq: forall s s' s'' st1 st2 z, execBs s st1 s' -> execBs s' st2 s'' -> execBs s (SeqInd inv  z st1 st2) s''.

(*TODO the proof *)
(*this is true as in the program expression auxiliary  variables never occur *)
Axiom  progExprEvalProp1 : 
forall ( sAux1  sAux2 : AuxState ) ( state : State) (expr : NumExpr ) ,
( neval  state sAux1 expr ) =  ( neval  state sAux2 expr ).
 



End semantique.

