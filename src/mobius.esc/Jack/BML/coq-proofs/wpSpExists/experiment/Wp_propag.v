Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Require Import BasicDef.
Require Import Logic_n.
Require Import Language.
Require Import Semantic.

Open Scope Z_scope.

Fixpoint wp_propag_stmt (i:stmt) ( post : assertion )(s:state) 
                                                 {struct i} : Prop :=
 match i with
 
 | Affect z x e => post (update s x (eval_expr s e))

 | If z e stmtT stmtF =>
    (eval_expr s e <> 0 -> wp_propag_stmt stmtT post s) /\
    (eval_expr s e = 0 -> wp_propag_stmt stmtF post s)

 | While z e (Inv inv modi) stmt =>
     inv s /\
    (forall s', 
       eval_expr s' e <> 0 ->
       inv s' -> 
       (forall x, ~In x modi -> s' x = s x) ->
       wp_propag_stmt stmt 
         (fun s'' => inv s'' /\ (forall x, ~In x modi -> s'' x = s x)) s') /\
    (forall s', 
       eval_expr s' e = 0 ->
       inv s' -> 
       (forall x, ~In x modi -> s' x = s x) -> post s')

 | Snil z => post s 

 | Sseq z i stmt => wp_propag_stmt i (wp_propag_stmt stmt post) s 
 
end.


Lemma wp_monotone : forall stmt (post1 post2:assertion),
   (forall s, post1 s -> post2 s) -> 
   forall s, wp_propag_stmt stmt post1 s -> wp_propag_stmt stmt post2 s.
Proof.
  induction stmt;
 (* induction stmt using stmt_ind_mut with 
  (P := fun i => forall (post1 post2:assertion),
        (forall s, post1 s -> post2 s) -> 
        forall s, wp_propag_stmt i post1 s -> wp_propag_stmt i post2 s); *)
 simpl wp_propag_stmt;simpl wp_propag_stmt;intros;auto.
 destruct H0 as (HT,HF);split;intros.
 apply (IHstmt1 post1 post2);auto.
 apply (IHstmt2 post1 post2);auto.
 destruct i as (inv,modi).
 destruct H0 as (Hinit, (Hpreserve, Hfinal)).
 repeat split;intros;auto.
 assert (H1 := IHstmt2 post1 post2  H);auto.
 apply (IHstmt1  (wp_propag_stmt stmt2 post1 )  ). 
 assumption.
 assumption.
Qed.
(*
Lemma wp_monotone_instr : forall i (post1 post2:assertion),
   (forall s, post1 s -> post2 s) -> 
   forall s,  wp_propag_stmt  i post1  s -> wp_propag_stmt i post2 s.
Proof.
 induction i using instr_ind_mut with 
  (P0 := fun stmt => forall (post1 post2:assertion),
   (forall s, post1 s -> post2 s) -> 
   forall s, wp_propag_stmt stmt post1 s -> wp_propag_stmt stmt post2 s);
 simpl wp_propag_instr;simpl wp_propag_stmt;intros;auto.
 destruct H0 as (HT,HF);split;intros.
 apply (IHi post1 post2);auto.
 apply (IHi0 post1 post2);auto.
 destruct i as (inv,modi).
 destruct H0 as (Hinit, (Hpreserve, Hfinal)).
 repeat split;intros;auto.
 apply (IHi (wp_propag_stmt s post1));auto.
 intros s1 Hs1;apply (IHi0 post1);auto.
Qed.
*) 

Lemma wp_stmt_correct : forall s1 s2 stmt,
   exec_stmt s1 stmt s2 ->
   forall post,
   wp_propag_stmt stmt post s1 -> post s2.
Proof.
 intros s1 s2 stmt.
 intros exec;
 induction exec; simpl; auto.
(* if *)
 
 (* then case *)
 intros post wpIf;
 apply (IHexec  post);auto.
 destruct wpIf as ( wpT,  wpF).
 apply wpT. assumption.
 
 (* else case *)
 intros post wpIf. 
 apply (IHexec  post);auto.
 destruct wpIf as ( wpT,  wpF).
 apply wpF. assumption.

 (*while*) 
 (*iteration*)
 intros post. 
 destruct inv as [ invariant modifies] .
 intros (Hinit, (Hpreserve, Hfinal)).
 apply (IHexec2 post).
 assert ( H2 := Hpreserve s1  H Hinit   (fun x H => refl_equal (s1 x)) ).
 assert ( invHoldsInS2 := IHexec1  
                                              (fun s'' : state => 
                                              invariant s'' /\ (forall x : var, ~ In x modifies -> s'' x = s1 x)) H2 ). 
 simpl in *.
 destruct invHoldsInS2 as ( inv , modi).
 repeat split;intros.
 auto.
 apply wp_monotone with (post1 := (fun s'' : state =>
                 invariant s'' /\ (forall x : var, ~ In x modifies -> s'' x = s1 x)));
 auto.
 intros s (Hinv, Heq);split;intros;auto.
 rewrite Heq;auto.
 symmetry; auto.
  
 apply Hpreserve;auto. intros. rewrite H3;auto.
 apply Hfinal;auto. intros;rewrite H3;auto.

 
 (* end case*)
 intros post. 
 destruct inv as [ invariant modifies] .
 intros (Hinit, (Hpreserve, Hfinal)).
 apply (Hfinal s1 ); auto.

 (* Cas stmt *)
 intros post H.  
 apply (IHexec2 post).
 apply (IHexec1 _ H).
Qed.



Definition correct_prog (p : prog) := 
 let (pre,stmt,post) := p in
 forall s, pre s -> wp_propag_stmt stmt (post s) s.

Lemma correction : forall p, 
  correct_prog p ->
  let (pre,stmt,post) := p in
  forall s1 s2, exec_stmt s1 stmt s2 -> pre s1 -> post s1 s2.
Proof.
 intros (pre,stmt,post) Hcorrect s1 s2 Hexec Hpre.
 apply (wp_stmt_correct _ _ _ Hexec (post s1)).
 simpl in Hcorrect. 
 apply Hcorrect;trivial.
Qed.
