Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import Language.
Require Import Logic.
Require Import Semantic.
Require Import Logic_n.
Require Import BasicDef.


Fixpoint wp_stmt  (i:stmt) (post:assertion)  {struct i} : prodT assertion  listP :=
 match i  with
 | Affect x e =>   pairT (fun s => post (update s x (eval_expr s e))) nilP

 | If  e stmtT stmtF =>  
   let (preT,annexT ) := wp_stmt  stmtT post in
   let (preF,annexF ) := wp_stmt  stmtF post in
   pairT 
    (fun s =>  ( (eval_expr s e <> 0)   ->  (preT s) )   
                      /\ 
                     ( (eval_expr s e = 0) -> (preF s) ) )
     (appendP annexT annexF)

 | While e inv stmt => 
   let (invariant, _ ):= inv in 
   let (preB, annexB) := wp_stmt  stmt invariant in
   let aPreserve :=
         forall s, eval_expr s e <> 0 ->  (invariant s) ->  (preB s) in
   let aPost :=	
         forall s, eval_expr s e = 0  ->  (invariant s) -> (post s) in
   pairT invariant  (consP aPreserve (consP aPost annexB))

 | Snil  => pairT post nilP

 | Sseq i stmt => 
   let (preS, annexS) := wp_stmt  stmt post in
   let (preI, annexI) := wp_stmt  i preS in
   pairT preI (appendP annexI annexS)     
 end.


(*commented as the proof is too technical , TODO *)
(* Lemma wp_stmt_correct : forall  s1 s2 stmt,
  exec_stmt s1 stmt s2 ->
  forall post:assertion,
  let (pre, annex) := wp_stmt  stmt post in
  (forall P, InP P annex -> P) ->
  ( (pre s1) -> (post s2)).
Proof.
 intros s1 s2 stmt exec; induction exec; 
 simpl;intros;auto.
 assert ( IHexec1 := IHexec post).
 destruct (wp_stmt  stmtT post) as (preT, annexT);
 destruct (wp_stmt  stmtF post) as (preF, annexF);simpl;intros.
 apply IHexec1. 
 assert ( goal :=  InP_appendP_l annexT annexF H0 ) .
 assumption.
 destruct H1 as (H1 , H2). 
 apply H1.
 assumption.

 assert ( IHexec1 := IHexec post).
 destruct (wp_stmt  stmtT post) as (preT, annexT);
 destruct (wp_stmt  stmtF post) as (preF, annexF);simpl;intros.
 apply IHexec1. 
 assert ( goal :=  InP_appendP_r annexT annexF H0 ) .
 assumption.
 destruct H1 as (H1 , H2). 
 apply H2.
 assumption.

 (* while *)
 destruct  inv  as (invariant, list ).
 assert ( IH2 := IHexec2 post).
 assert ( IH1 := IHexec1 invariant).
 destruct (wp_stmt  stmt invariant ) as (preB, annexB).
 intros. 
 destruct (  wp_stmt stmt post  )as ( preBody , annexBody).
 destruct (   wp_stmt (While e (Inv invariant list) stmt) post ) as (preWhile , annexWhile). 
 
 apply (IH2).
 (* Up To Here *)

 apply (mkProd_imp_imp  (invariant s2)).
 apply (mkProd_imp_imp n (preB s1)).
 let t := 
   constr:(H0 
    (forall s : state, eval_expr s e <> 0 -> mkProd_imp n (inv s) (preB s))) in
 let T := type of t in
 match eval lazy beta iota delta [InP] in T with
 | ?P = ?P \/ ?Q -> _=> 
   assert (H2 := t (or_introl Q (refl_equal P))); auto
 end.
 apply IHstmt; intros;apply H0;simpl;auto.
 apply (IHexec_stmtIndex0 post H0).
 destruct (wp_stmt n stmt inv) as (preB, annexB);intros.
 let t := 
   constr:(H
     (forall s : state, eval_expr s e = 0 -> mkProd_imp n (inv s) (post s))) in
 let T := type of t in
 match eval lazy beta iota delta [InP] in T with
 | ?P1 \/ (?P = ?P \/ ?Q) -> _=> 
   assert (H2 := t (or_intror P1 (or_introl Q (refl_equal P)))); auto
 end.
 assert (H1:= IHexec_stmtIndex (fun s _ : state => post s)). 
 clear IHexec_stmtIndex.
 destruct (wp_stmt (S n) stmt (fun s _ : state => post s)) as (pre, annex).
 intros H2; exact (H1 H2 s1).
 assert (H1 := IHexec_stmtIndex0 post);clear IHexec_stmtIndex0.
 destruct (wp_stmt n stmt post) as (preS, annexS).
 assert (H2 := IHexec_stmtIndex preS);clear IHexec_stmtIndex.
 destruct (wp_stmt n i preS) as (preI, annexI).
 intros H0. apply (mkProd_imp_imp n (preS s2)).
 apply H2;exact (InP_appendP_l _ _ H0).
 apply H1;exact (InP_appendP_r _ _ H0).
Qed.



Lemma wp_prog_correct : forall s1 s2 stmt,
  exec_stmtIndex 0 s1 stmt s2 ->
  forall post:assertion,
  let (pre, annex) := wp_stmt 0 stmt post in
  (forall P, InP P annex -> P) ->
  pre s1 -> post s2.
Proof. exact (wp_stmt_correct O). Qed. *)

