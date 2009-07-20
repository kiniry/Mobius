Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import BasicDef.
Require Import Logic_n.
Require Import Language.
Require Import Semantic.

Fixpoint wp_instrA (i:instrA) (post: invA) {struct i} : prodT invA listP :=
 match i with 
 | AffectA x e => 
   pairT (fun s aux => post (update s x (eval_expr s e)) aux) nilP

 | IfA e stmtT stmtF =>
   let (preT,annexT) := wp_stmtA stmtT post in
   let (preF,annexF) := wp_stmtA stmtF post in
   let pre := 
     fun s aux =>
         (eval_expr s e <> 0 -> preT s aux) 
      /\ (eval_expr s e = 0  -> preF s aux)
   in
   pairT pre (appendP annexT annexF)

 | WhileA e inv stmt =>
   let (preB, annexB) := wp_stmtA stmt inv in
   let aPreserve :=
     forall s aux, eval_expr s e <> 0 -> inv s aux -> preB s aux in
   let aPost :=	
     forall s aux, eval_expr s e = 0  -> inv s aux -> post s aux in
   pairT inv (consP aPreserve (consP aPost annexB))

 | SetA p => 
   let pre := fun s aux => post s (updateA aux p s) in
   pairT pre nilP

 end

with wp_stmtA (stmt:stmtA) (post: invA) {struct stmt} : prodT invA listP :=
 match stmt with 
 | SnilA => pairT post nilP

 | SseqA i stmt =>
   let (preS, annexS) := wp_stmtA stmt post in
   let (preI, annexI) := wp_instrA i preS in
   pairT preI (appendP annexI annexS)     
 end.



Lemma wp_stmtA_correct : forall s1 aux1 stmt s2 aux2,
  exec_stmtA s1 aux1 stmt s2 aux2 ->
  forall (post:invA),
  let (pre, annex) := wp_stmtA stmt post in
  (forall P, InP P annex -> P) ->
  pre s1 aux1 -> post s2 aux2.
Proof.
 induction 1 using exec_stmtA_ind_mut with
   (P := fun s1 aux1 i s2 aux2 (H:exec_instrA s1 aux1 i s2 aux2) =>
           forall (post:invA),
           let (pre, annex) := wp_instrA i post in
           (forall P, InP P annex -> P) ->
           pre s1 aux1 -> post s2 aux2);
 simpl;intros;auto.
  
 (* cas if true *)
 assert (HT := IHexec_stmtA post); clear IHexec_stmtA.
 destruct (wp_stmtA stmtT post) as (preT, annexT).
 destruct (wp_stmtA stmtF post) as (preF, annexF).
 intros HP (HimpT, HimpF).
 apply HT;auto. apply (InP_appendP_l _ _ HP).

 (* cas if false *)
 assert (HF := IHexec_stmtA post); clear IHexec_stmtA.
 destruct (wp_stmtA stmtT post) as (preT, annexT).
 destruct (wp_stmtA stmtF post) as (preF, annexF).
 intros HP (HimpT, HimpF).
 apply HF;auto. apply (InP_appendP_r _ _ HP).

 (* Cas while true *)
 assert (IHstmt := IHexec_stmtA inv);clear IHexec_stmtA.
 simpl in IHexec_stmtA0.
 destruct (wp_stmtA stmt inv) as (preB, annexB).
 intros HP Hinv. 
 apply (IHexec_stmtA0 post);auto.
 apply IHstmt. intros;apply HP;simpl;auto.
 let t := 
   constr:(HP 
    (forall s aux, eval_expr s e <> 0 -> inv s aux -> preB s aux)) in
 let T := type of t in
 match eval lazy beta iota delta [InP] in T with
 | ?P = ?P \/ ?Q -> ?P => 
   assert (H2 := t (or_introl Q (refl_equal P))); auto
 end.

 (* cas while false *)
 destruct (wp_stmtA stmt inv) as (preB, annexB);intros HP Hinv.
 let t := 
    constr:(HP 
    (forall s aux, eval_expr s e = 0 -> inv s aux -> post s aux)) in
 let T := type of t in
 match eval lazy beta iota delta [InP] in T with
 | ?P1 \/ (?P = ?P \/ ?Q) -> _=> 
   assert (H2 := t (or_intror P1 (or_introl Q (refl_equal P)))); auto
 end.

 (* Cas Sequence *)

 assert (Hstmt := IHexec_stmtA0 post);clear IHexec_stmtA0.
 destruct (wp_stmtA stmt post) as (preS, annexS).
 assert (Hi := IHexec_stmtA preS);clear IHexec_stmtA.
 destruct (wp_instrA i preS) as (preI, annexI).
 intros HP Hpre.
 apply Hstmt. apply (InP_appendP_r _ _ HP).
 apply Hi;auto. apply (InP_appendP_l _ _ HP).
Qed.


Definition correct_progA (p:progA) := 
 let (pre,stmt,post) := p in
 forall s,
   let (preW, annex) := wp_stmtA stmt (fun s' aux => post s s') in
   (forall P, InP P annex -> P) /\
   forall aux, pre s -> preW s aux.

Lemma correctionA : forall p, 
  correct_progA p ->
  let (pre,stmt,post) := p in
  forall s1 aux1 s2 aux2, 
  exec_stmtA s1 aux1 stmt s2 aux2 -> pre s1 -> post s1 s2.
Proof.
 intros (pre,stmt,post) Hcorrect s1 aux1 s2 aux2 Hexec Hpre.
 assert (H := wp_stmtA_correct _ _ _ _ _ Hexec (fun s' aux => post s1 s')).
 assert (H0 := Hcorrect s1).
 destruct (wp_stmtA stmt (fun (s' : state) (_ : stateA) => post s1 s')).
 destruct H0;apply H;auto.
Qed.

(*commented Mariela 27 02 06*)
Axiom wp_stmtA_monotone : forall stmt (post1 post2:invA),
           (forall s aux, post1 s aux -> post2 s aux) -> 
           let (pre1, annex1) := wp_stmtA stmt post1 in
           let (pre2, annex2) := wp_stmtA stmt post2 in 
              ((forall P, InP P annex1 -> P) -> (forall P, InP P annex2 -> P)) 
           /\ (forall s aux, pre1 s aux -> pre2 s aux).
(* Proof.
 induction stmt using stmtA_ind_mut with 
  (P := fun i => forall (post1 post2:invA),
        (forall s aux, post1 s aux -> post2 s aux) -> 
           let (pre1, annex1) := wp_instrA i post1 in
           let (pre2, annex2) := wp_instrA i post2 in 
              ((forall P, InP P annex1 -> P) -> (forall P, InP P annex2 -> P)) 
           /\ (forall s aux, pre1 s aux -> pre2 s aux));
 simpl;intros;auto.
 (* Cas if *)
 assert (Hstmt1 := IHstmt1 _ _ H);clear IHstmt1.
 assert (Hstmt2 := IHstmt2 _ _ H);clear IHstmt2.
 destruct (wp_stmtA stmt1 post1) as (preT1, annexT1);
 destruct (wp_stmtA stmt2 post1) as (preF1, annexF1);
 destruct (wp_stmtA stmt1 post2) as (preT2, annexT2);
 destruct (wp_stmtA stmt2 post2) as (preF2, annexF2).
 destruct Hstmt1;destruct Hstmt2.
 split.

(*added Mariela: Hin does not exist*)
intros H5 .
(*end Added Mariela*)
apply H0.  assert ( AS := InP_appendP_l _ _ H5). trivial.
apply H2.  assert  (AS := InP_appendP_r _ _ H5 ). trivial.

intros s aux (HT, HF);split;auto.

 (* Cas While *)
 clear IHstmt.
 destruct (wp_stmtA stmt i) as (pre, annex).
 split;auto.
 simpl;intros.
 destruct H1. apply (H0 P);auto.
 destruct H1. 
 rewrite H1;assert (forall (s : state) (aux : stateA),
                      eval_expr s e = 0 -> i s aux -> post1 s aux).
 apply H0;auto. 
 auto.
 apply H0;auto.

 (* Cas Sseq *)
 assert (Hcont := IHstmt0 _ _ H);clear IHstmt0.
 destruct (wp_stmtA stmt post1) as (preS1, annexS1);
 destruct (wp_stmtA stmt post2) as (preS2, annexS2);
 destruct Hcont.
 assert (Hi := IHstmt _ _ H1);clear IHstmt.
 destruct (wp_instrA i preS1) as (preI1, annexI1);
 destruct (wp_instrA i preS2) as (preI2, annexI2);
 destruct Hi.
 split;trivial.
 intros Hin;apply (InP_appendP annexI2 annexS2).
 apply H2;apply (InP_appendP_l _ _ Hin).
 apply H0;apply (InP_appendP_r _ _ Hin).
Qed.

*)
















































(*
Fixpoint wp_instrG (n:nat) (i:instrG n) (post: assertionIndex (S n)) 
               {struct i} : prodT (assertionIndex (S n)) listP :=
  match i with 
 | AffectG x e => 
   pairT (fun s => post (update s x (eval_expr s e))) nilP

 | IfG e stmtT stmtF =>
   let (preT,annexT) := wp_stmtG n stmtT post in
   let (preF,annexF) := wp_stmtG n stmtF post in
   let pre := 
     fun s =>
       let cond    := mkLambda n (eval_expr s e <> 0) in
       let notcond := mkLambda n (eval_expr s e = 0) in
       mkAnd n (mkImp n cond (preT s)) (mkImp n notcond (preF s))
   in
   pairT pre (appendP annexT annexF)

 | WhileG e inv stmt =>
   let (preB, annexB) := wp_stmtG n stmt inv in
   let aPreserve :=
     forall s, eval_expr s e <> 0 -> mkProd n (mkImp n (inv s) (preB s)) in
   let aPost :=	
     forall s, eval_expr s e = 0  -> mkProd n (mkImp n (inv s) (post s)) in
   pairT inv (consP aPreserve (consP aPost annexB))

 | DeclareG p => 
   let pre := fun s => mkImp n (mkEq s p n) (post s) in
   pairT pre nilP

 end

with wp_stmtG (n:nat) (stmt:stmtG n) (post: assertionIndex (S n)) 
            {struct stmt} : prodT (assertionIndex (S n)) listP :=
 match stmt with 
 | SnilG => pairT post nilP

 | SseqG i stmt =>
   let (preS, annexS) := wp_stmtG n stmt post in
   let (preI, annexI) := wp_instrG n i preS in
   pairT preI (appendP annexI annexS)     
 end.

Hint Resolve mkProd_mkImp_refl mkProd_and_l mkProd_and_r mkProd_mkImp
  mkProd_mkLambda.

Lemma wp_stmt_correct : forall n s1 s2 stmt,
  exec_stmtG n s1 stmt s2 ->
  forall post:assertionIndex (S n),
  let (pre, annex) := wp_stmtG n stmt post in
  (forall P, InP P annex -> P) ->
  mkProd n (mkImp n (pre s1) (post s2)).
Proof.
 intro n; induction 1 using exec_stmtG_ind_mut with 
  (P := fun s1 i s2 (H:exec_instrG n s1 i s2) =>
           forall post:assertionIndex (S n),
           let (pre, annex) := wp_instrG n i post in
           (forall P, InP P annex -> P) ->
           mkProd n (mkImp n (pre s1) (post s2)));
 simpl;intros;auto.

 (* cas if true *)
 assert (HT := IHexec_stmtG post); clear IHexec_stmtG.
 destruct (wp_stmtG n stmtT post) as (preT, annexT).
 destruct (wp_stmtG n stmtF post) as (preF, annexF).
 intros HP.
 apply mkProd_imp_imp with (H1 := preT s1).
 apply mkProd_imp_imp with 
   (H1 := mkImp n (mkLambda n (eval_expr s1 e <> 0)) (preT s1));auto.
 apply HT;apply (InP_appendP_l _ _ HP).

 (* cas if false *)
 assert (HF := IHexec_stmtG post); clear IHexec_stmtG.
 destruct (wp_stmtG n stmtT post) as (preT, annexT).
 destruct (wp_stmtG n stmtF post) as (preF, annexF).
 intros HP.
 apply mkProd_imp_imp with (H1 := preF s1).
 apply mkProd_imp_imp with 
   (H1 := mkImp n (mkLambda n (eval_expr s1 e = 0)) (preF s1));auto.
 apply HF;apply (InP_appendP_r _ _ HP).

 (* Cas while true *)
 assert (IHstmt := IHexec_stmtG inv);clear IHexec_stmtG.
 simpl in IHexec_stmtG0.
 destruct (wp_stmtG n stmt inv) as (preB, annexB).
 intros HP. 
 apply (mkProd_imp_imp n (inv s2)).
 apply (mkProd_imp_imp n (preB s1)).
 let t := 
   constr:(HP 
    (forall s : state, eval_expr s e <> 0 -> 
                       mkProd n (mkImp n (inv s) (preB s)))) in
 let T := type of t in
 match eval lazy beta iota delta [InP] in T with
 | ?P = ?P \/ ?Q -> ?P => 
   assert (H2 := t (or_introl Q (refl_equal P))); auto
 end.
 apply IHstmt; intros;apply HP;simpl;auto.
 apply (IHexec_stmtG0 post HP).

 (* cas while false *)
 destruct (wp_stmtG n stmt inv) as (preB, annexB);intros HP.
 let t := 
    constr:(HP 
    (forall s : state, eval_expr s e = 0 -> 
                       mkProd n (mkImp n (inv s) (post s)))) in
 let T := type of t in
 match eval lazy beta iota delta [InP] in T with
 | ?P1 \/ (?P = ?P \/ ?Q) -> _=> 
   assert (H2 := t (or_intror P1 (or_introl Q (refl_equal P)))); auto
 end.


*)











