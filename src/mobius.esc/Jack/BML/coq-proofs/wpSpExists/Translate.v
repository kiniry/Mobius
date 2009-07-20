Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Require Import BasicDef.
Require Import Logic_n.
Require Import Language.
Require Import Semantic.
Require Import Wp_propag.
Require Import Wp.
Require Import Classical.
Require Import helperTranslate.
Require Import axioms.

(*Require Import WpG.*)
(* Definition substT := stateA -> state.*)

(* Definition invSP := stateA -> Prop.*)

Set Implicit Arguments.

Inductive tripleT (A B C : Type) : Type :=  
 | triple : A -> B -> C -> tripleT A B C .

Unset Implicit Arguments.


Fixpoint translate (pre : assertion ) (st :stmt) {struct st}: tripleT stmt  assertion listP  :=
 match st with 
 |  (Affect x e) =>
    let SP :=  fun s => exists state,   pre ( state )  
                                               /\   
                                               ( s x )  = ( eval_expr state   e  ) 
                                               /\  forall y, x <> y -> ( s y ) = (state y)   in

    
    ( triple ( Affect x e)  SP  nilP)
 |  (If e bT bF) =>
    let preT :=
	fun s => 
	     	pre s  /\   eval_expr s e <> 0  in
    let (   btT , SPT  , annexT ) := translate  preT bT   in
    let preF  :=
	fun s =>  
     	pre s /\ eval_expr s e = 0  in
    let (btF , SPF  , annexF ) := translate  preF bF   in
    let SP := fun s => SPT s \/ SPF s in
    let annex :=  appendP annexT annexF in
    (  triple ( If e btT btF)  SP annex)
 
 |  (While e (Inv inv l) body)    =>
    let invA  := fun s =>exists statePre, 
                        ( inv s /\ 
                        ( forall x, ~In x l -> s x = statePre x) /\ 
                        ( pre statePre ) ) in
    let (bodyT , SPB , annexB) :=   
    let preBody  := fun s => 
                               exists statePre,  
                               ( eval_expr  s e <> 0 /\ 
                               ( inv s ) /\ 
                               ( forall x, ~In x l -> s x = statePre x) /\ 
                               ( pre statePre ) )  in
     translate  preBody  body  in
     let SP :=  fun s => 
                               exists statePre,  
                               ( eval_expr  s e =  0 /\ 
                               ( inv s ) /\ 
                               ( forall x, ~In x l -> s x = statePre x) /\ 
                               ( pre statePre ) )   in
     let annex1 := forall s, pre s -> invA s in
     let annex2 := forall s, SPB s -> invA s in
     let annex := ( consP annex1 (consP annex2 annexB ) ) in 
    ( triple (While e ( Inv invA nil) bodyT )  SP annex )
  
 |  Snil => (triple   Snil  pre nilP ) 
 
 |  Sseq st1 st2 =>
    let (stT1, SP1, annex1 )  :=  translate pre st1    in
    let (stT2, SP2, annex2 )  :=  translate SP1 st2 in
    let annex := appendP annex1  annex2 in
    ( triple  (Sseq stT1 stT2 )  SP2  annex)
 end.



    
(* 
Lemma translate_imp : 
  forall stmt n (pre:invSP) subst,
    let (stmtA, p, postA, substA) := translate n pre subst stmt in
    forall aux, postA aux -> pre aux.
Proof.
 induction stmt using translate_ind;simpl;intros;auto.
 match goal with 
 | |- context [translate ?N ?P ?S ?STM] =>
   assert (Hstmt := IHstmt N P S);clear IHstmt;
   destruct (translate N P S STM) as (contA, p, postcont, substcont);
   auto
 end.
 match goal with 
 | |- context [translate ?N ?P ?S stmt2] =>
   assert (Hstmt2 := IHstmt2 N P S);clear IHstmt2;
   destruct (translate N P S stmt2) as (bAT, p, postT, substT0)
 end.
 match goal with 
 | |- context [translate ?N ?P ?S stmt3] =>
   assert (Hstmt3 := IHstmt3 N P S);clear IHstmt3;
   destruct (translate N P S stmt3) as (bAF, q, postF, substF)
 end.
 match goal with 
 | |- context [translate ?N ?P ?S stmt1] =>
   assert (Hstmt1 := IHstmt1 N P S);clear IHstmt1;
   destruct (translate N P S stmt1) as (contA, q', postcont, substcont)
 end.
 intros aux Hpost;destruct (Hstmt1 _ Hpost).
 destruct (Hstmt2 _ H);trivial.
 destruct (Hstmt3 _ H);trivial.
 match goal with 
 | |- context [translate ?N ?P ?S stmt2] =>
   assert (Hstmt2 := IHstmt2 N P S);clear IHstmt2;
   destruct (translate N P S stmt2) as (bodyA, p, postB, substB)
 end.
 match goal with 
 | |- context [translate ?N ?P ?S stmt1] =>
   assert (Hstmt1 := IHstmt1 N P S);clear IHstmt1;
   destruct (translate N P S stmt1) as (contA, q, postcont, substcont)
 end.
 intros aux Hcont; assert (H:= Hstmt1 _ Hcont);intuition.
Qed.
*)



Lemma toto : forall ( st : stmt) 
                                 (pre: assertion)  post,
    let (stmtT , SP , annex ) := translate pre st in 
    ( forall s, (pre s -> wp_propag_stmt st post s) ) ->
    ( (forall s, SP s -> post s  )  /\   forall P,  (  InP P annex ) ->   P )  .

Proof.
  intros stmt; induction stmt; intros pre post; simpl; auto.
  intros  pre_impl_wp  .
  
  (*assign case*)
  split.
  intros s SpHolds.
  elim SpHolds. 
  intros state sp. 
  clear SpHolds. 
  destruct sp as ( pre_in_state , ( v_in_s , y_in_s )).
  assert ( stateEqs : forall v1 , s v1 = ( update state v ( eval_expr state e ) ) v1  ).
  intros v0.
  unfold update.
  caseEq (eq_var v v0).
 
  unfold eq_var .
  intros eqv_v0.
  assert ( v_eq_v0 :=  Zeq_bool_implies_eq v v0 eqv_v0 ).
  clear eqv_v0.
  rewrite <-   v_eq_v0.
  assumption.
  unfold eq_var. 
  intros neqv_v0.
  assert ( v_neq_v0 := Zneq_bool_implies_neq v v0 neqv_v0).  
  assert ( sv_eq_statev := y_in_s v0 v_neq_v0).
  assumption.
  assert ( stateEqext := extentional var _ s ( update state v ( eval_expr state e )) stateEqs ).  
  rewrite stateEqext.
  apply pre_impl_wp.
  assumption.
  intros.  elim H.
 (* if case*)
  assert (IHst1 := IHstmt1 ( fun s : state => pre s /\ eval_expr s e <> 0) post).
  clear IHstmt1.
  assert (IHst2 := IHstmt2 ( fun s : state => pre s /\ eval_expr s e = 0) post).
  clear IHstmt2.

  destruct ( translate ( fun s : state => pre s /\ eval_expr s e <> 0) stmt1 ) as (btT , SPT, annexT). 
  destruct ( translate ( fun s : state => pre s /\ eval_expr s e = 0 ) stmt2 ) as ( btF, SPF, annexF).
  intros    pre_implies_wp. 
  assert (Hyp1 : ( forall s, (  pre s ) /\ (eval_expr s e <> 0 ) -> ( wp_propag_stmt stmt1 post s ) ) /\
                ( forall s, (pre s ) /\ (eval_expr s e = 0)  -> ( wp_propag_stmt stmt2 post s ) )). 
  
  
  split. 
  intros s H.
  destruct H.
  assert ( pre_implies_wp_in_s := pre_implies_wp s H). 
  destruct pre_implies_wp_in_s as ( H1 , H2).  
  apply H1.
  assumption.
  intros s H.
  destruct H as (H, H1).
  assert ( pre_implies_wp_in_s := pre_implies_wp s H).
  destruct pre_implies_wp_in_s as ( H2 , H3).  
  apply H3.
  assumption.
  destruct Hyp1 as ( thenH , elseH).
  clear pre_implies_wp.

  assert ( IHS1 := IHst1  thenH ).
  assert (IHS2 := IHst2 elseH).
  destruct IHS1 as ( SpTH , annT).
  destruct IHS2 as ( SpFH , annF).
  
  split.
  intros s SPif.
  destruct SPif.
  apply SpTH.
  assumption. 
  apply SpFH.
  assumption. 
  assert ( Hyp2 := InP_appendP  annexT annexF annT annF). 
  assumption.
  

  (* while *)
  destruct i as (inv, lMod).
  assert (Ih :=IHstmt (fun s : state =>
           exists statePre : var -> value,
             eval_expr s e <> 0 /\
             inv s /\
             (forall x : var, ~ In x lMod -> s x = statePre x) /\
             pre statePre)).
  destruct    
             ( translate  (fun s : state =>
             exists statePre : var -> value,
             eval_expr s e <> 0 /\
             inv s /\
             (forall x : var, ~ In x lMod -> s x = statePre x) /\
             pre statePre) stmt ) as (_, SPB, annexB). 
  intros pre_implies_wp.
  split. 
  (*the propagated postcondition implies the postcondition *)
  intros s.
  intros Hyp.
  elim Hyp.
  intros.
  assert ( pre_wp1  :=    pre_implies_wp x).
  destruct H as ( condF , (inv_in_s , ( notMod , pre_in_x)) ).
  assert ( pre_wp2 :=  pre_wp1 pre_in_x  ). 
  destruct pre_wp2 as ( inv_x , ( presInv, inv_post )).
  apply inv_post.
  assumption.
  assumption.
  assumption.

  intros P listP.
  unfold InP in listP.
  destruct listP.
  rewrite H.

 (*the precondition implies the new invariant*)
  clear H.
  intros s.
  intros pre_s.
  exists s.    
  assert ( pre_wp1 := pre_implies_wp s pre_s). 
  destruct pre_wp1 as ( inv_s, ( presInv, inv_post )).
  split. assumption.
  split.
  intros. trivial.
  assumption.

  (* the sp_body implies the new  invariant*)
  (* destruct H.  
      rewrite H. *)
  (* intros s SPBody. *)
  (*get the hypothesis that the inv, the cond,
    pre and the condition on the nonmodified variables implie the wp over the 
    body and as postcondition the old invariant *)
  assert (indHyp : forall s  s', pre s /\ 
                                    eval_expr s' e <> 0 /\
                                    inv s' /\
                                    (forall x : var, ~ In x lMod -> s' x = s x) ->
                                         ( wp_propag_stmt stmt
                                         (fun s'' : state =>
                                         inv s'' /\ (forall x : var, ~ In x lMod -> s'' x = s x)) s' 
                                          )  ).
  intros.
  destruct H0 as ( H0 , (cond_s, (inv_s' , mod_s'))).
  assert (pre_wp1 := pre_implies_wp s H0).
  destruct pre_wp1 as ( invs0 , ( presH, invPostH)).
  apply presH. 
  assumption.
  assumption.
  assumption.
    
  assert ( indHyp1 :    forall s s' ,
         pre s /\
         eval_expr s' e <> 0 /\
         inv s' /\
         (forall x : var, ~ In x lMod -> s' x = s x) ->
         wp_propag_stmt stmt
           (fun s'' : state =>
             inv s'' /\ (forall x : var, ~ In x lMod -> s'' x = s x) /\ ( pre s ) ) s' ) .
  intros s . 
  assert ( preInPost := PropInPost 
                        pre
                        stmt 
                        ( fun s' => eval_expr s' e <> 0 /\ inv s' /\  (forall x : var, ~ In x lMod -> s' x = s x)  )
                        ( fun s'' : state =>  inv s'' /\ (forall x : var, ~ In x lMod -> s'' x = s x) ) 
                        s
). 
  simpl in *.


  (*new *)

  assert ( indHyp1 := preInPost ( indHyp  s )).
  intros.
  assert (assoc := conjAssoc inv 
                                                  (fun state => forall x:  var, ~ In x lMod -> state x = s x  )
                                                  ( fun  state => pre s)  ).

  simpl in assoc. 
  rewrite assoc in indHyp1.
  clear assoc.
  assert( indHyp2 := indHyp1 s' H0).
  assumption.
(* up to here reasonable *)
  assert ( indHyp2 := existsInPost1 stmt inv pre lMod).

  assert (H7: forall st s: state ,  
     (  pre st /\ 
     eval_expr s e <> 0 /\ 
     inv s /\ 
     forall x:  var, ~ In x lMod -> s x = st x  ) -> 
     ( wp_propag_stmt 
       stmt
       (fun s : state => exists st: state,  inv s /\  
                       ( forall x:  var, ~ In x lMod -> s x = st x  ) /\ 
                       pre st) s)
                       ).
  intros st s prec. 
  apply ( indHyp2 st s).
  apply ( indHyp1 st s).
  intuition. 
  
  (*do tuk*)
  assert ( univ :=  univToEx 
                              stmt 
                              pre 
                              ( fun s => eval_expr s e <> 0 /\ inv s )   
                              (fun s0 : state => 
                                 exists st0: state ,  inv s0 /\ 
                                   ( forall x, ~ In x lMod  -> s0 x = st0 x  ) /\
                                   pre st0
                              )
                              lMod
                              
                   ).
  simpl in univ.
  assert ( H100 : forall s1 s2 , pre s1 /\ 
                                      ( eval_expr s2 e <> 0 /\ inv s2) /\ 
                                      ( forall x, ~ In x lMod  -> s2 x = s1 x  ) -> 
                                      pre s1 /\ 
                                      eval_expr s2 e <> 0 /\ inv s2/\ 
                                      ( forall x, ~ In x lMod  -> s2 x = s1 x  ) 
                                      ).
  intros. intuition. 
  
  assert ( H9:  forall s1 s2 , pre s1 /\ 
                                      ( eval_expr s2 e <> 0 /\ inv s2) /\ 
                                      ( forall x, ~ In x lMod  -> s2 x = s1 x  ) -> 
                                     ( wp_propag_stmt 
                                       stmt
                                       ( fun s0 : state => 
                                         exists st0, 
                                         inv s0 /\ ( forall x, ~ In x lMod  -> s0 x = st0 x ) /\ pre st0
                                       ) 
                                     ) s2 
   ).
  intros. 
  apply ( H7 s1 s2).

  intuition. 
  clear H100.                                  
  assert ( univ1 := univ H9 ).    
  clear H9.
  
  assert (IH := Ih 
   (  fun s0 => (exists st, inv s0 /\  ( forall x0: var, ~ In x0 lMod -> s0 x0 = st x0 )  /\ pre st) )  ).
  assert ( H101 : forall s2,
    (exists s1 : state,
            
           eval_expr s2 e <> 0 /\ inv s2 /\
           (forall x : var, ~ In x lMod -> s2 x = s1 x) /\ pre s1) -> 
  
    (exists s1 : state,
           pre s1 /\
           ( eval_expr s2 e <> 0 /\ inv s2 ) /\
           (forall x : var, ~ In x lMod -> s2 x = s1 x)) 
).

  intros s2 H102.
  elim H102. intros x H105.
  exists x.
  intuition.
  assert ( H102 : forall s2 : state,
       (exists s1 : state,
          eval_expr s2 e <> 0 /\
          inv s2 /\ (forall x : var, ~ In x lMod -> s2 x = s1 x) /\ pre s1) -> 
      wp_propag_stmt stmt
          (fun s0 : state =>
           exists st0 : state,
             inv s0 /\
             (forall x : var, ~ In x lMod -> s0 x = st0 x) /\ pre st0) s2
 ).
  intros s2 cond.
  apply ( univ1 s2).
  elim cond. 
  intros x condx.
  clear cond.
  exists x.
  intuition.
  clear H101.
  assert ( H111 := IH H102).
  destruct H111.
  destruct H.
  rewrite H.
  assumption.
  
  destruct annexB.
  inversion H.
  destruct H.
  apply H1.
  rewrite H.
  simpl ... auto.
  apply H1.
  simpl... auto.


  (* nil *)
  intros H1.
  split.
  assumption.
 
  intros P Faux.
  contradiction.

  (*seq*)
  assert (ih1 := IHstmt1 pre ( wp_propag_stmt stmt2 post)).
  clear IHstmt1.  
  destruct (translate pre stmt1 ) as (stT1 , SP1 , annex1). 
  assert ( ih2 :=  IHstmt2 SP1   post).
  clear IHstmt2.
  destruct (translate SP1 stmt2 ) as (stT2 , SP2 , annex2). 
  intros pre_impl_wp.
  assert ( ih11 := ih1 pre_impl_wp).
  destruct ih11 as (hstmt1, ann1).
  assert (ih22 := ih2 hstmt1).
  destruct ih22 as ( hstmt2, ann2).
  split.
  assumption.
  intros P inPannex.
  assert (inLorR :=  InPappendl1l2_InPl1_or_InPl2 annex1 annex2 P inPannex).
  destruct inLorR.
  apply ann1.
  assumption.
  apply ann2.
  assumption.
Qed.

 Lemma coco : forall (st: stmt)  
                                    (pre post : assertion) ,
    let (stmtT , SP , annexSP ) := translate pre st in
    let (wp, annexWP) := (wp_stmt stmtT post) in 
    ( (forall s, SP s -> post s )  /\   forall P,  (  InP P annexSP ) ->   P ) ->
    ( ( forall s , pre s -> wp s )  /\   forall P,  (  InP P annexWP ) ->   P ).

Proof.
  intros stmt; induction stmt; simpl; auto; 
  intros pre post. 
  (*assign*)
  intros sp_impl_post.
  split.
  intros s pre_s.
  destruct sp_impl_post  as ( sp ,annex).
  assert (H1 := sp (update s v (eval_expr s e))).
  apply H1.
  exists s.
  repeat split.
  assumption.
  unfold update.
  caseEq ( eq_var v v ).
  intros eq_.
  trivial.
  intros neq_.
  assert ( H2:= eqRefl v).
  rewrite H2 in neq_.
  discriminate  neq_.
  intros y v_neq_y.
  unfold update.
  caseEq ( eq_var v y ).
  intros v_eq_y.
  assert ( H2:= eq_v1v2_true v y v_eq_y).
  destruct v_neq_y.
  assumption.
  intros.
  trivial.
  intros P faux.
  contradiction.

  (*if*)
  assert ( ih1 := IHstmt1 (fun s=>   pre s /\  eval_expr s e <> 0) post ).
  assert ( ih2 := IHstmt2 (fun s=>   pre s /\  eval_expr s e = 0) post ).
  clear IHstmt1.
  clear IHstmt2.
 
  caseEq  ( translate (fun s : state => pre s /\ eval_expr s e <> 0) stmt1). 
  intros stT postT annT transT.
  rewrite transT in ih1.

 (* destruct  ( translate (fun s : state => pre s /\ eval_expr s e <> 0) stmt1) as  (btT, SPT, annexT). 
  *)
  caseEq ( translate (fun s : state => pre s /\ eval_expr s e = 0) stmt2).
  intros stF postF annF transF.
  rewrite transF in ih2.

  (*destruct ( translate (fun s : state => pre s /\ eval_expr s e = 0) stmt2) as  (btF, SPF, annexF).*)
  caseEq   (wp_stmt stT post).
  intros wpT  annexWPT  wpEqT.
  rewrite wpEqT in ih1.
  (* destruct (wp_stmt btT post) as (wpT, annexWPT ). *)
  (*destruct (wp_stmt btF post) as (wpF, annexWPF ). *)
  caseEq (wp_stmt stF post). 
  intros wpF  annexWPF  wpEqF.
  rewrite wpEqF in ih2.

  caseEq  (wp_stmt (If e stT stF) post) . 
  intros wp annexWP wpEq.
  simpl in wpEq.
  rewrite wpEqT in wpEq.
  rewrite wpEqF in wpEq.
  injection wpEq.
  intros annexWpEq wpEq1.
  intros cond. 
  destruct cond as (  sp_impl_post , annexSp).
  
  assert ( H44 : (forall s : state, postT s  -> post s) /\ (forall s : state, postF s  -> post s)   ).
  split.
  intros s postTs.
  apply ( sp_impl_post s).
  left.
  assumption.

  intros s postFs.
  apply ( sp_impl_post s).
  right.
  assumption.
  destruct H44 as ( H441, H442).
  
  assert ( HannT := InP_appendP_l annT annF annexSp). 
  assert ( HannF := InP_appendP_r annT annF annexSp). 
  assert (ih11 := ih1  ( conj H441 HannT)).
  assert (ih21 := ih2  ( conj H442 HannF)).
  rewrite <- wpEq1 .
  destruct ih11 as ( wpTH , annTH).
  destruct ih21 as ( wpFH , annFH).
  split.
  intros s prec. split.
  intros cond_s.
  apply wpTH.
  intuition.
  intros ncond_s.
  apply wpFH.
  intuition.
  clear wpTH wpFH.
  rewrite <- annexWpEq.
  assert ( annex := InP_appendP  annexWPT annexWPF annTH annFH).
  assumption.

  (*while *)
  destruct i as ( inv, l).
  
  assert (ih1:= IHstmt 
              (fun s : state =>
              exists statePre : var -> value,
              eval_expr s e <> 0 /\
              inv s /\
              (forall x : var, ~ In x l -> s x = statePre x) /\ pre statePre)
              
              (fun s : state =>
              exists statePre : var -> value,
              inv s /\
              (forall x : var, ~ In x l -> s x = statePre x) /\ pre statePre)
  ).
  clear IHstmt.

  caseEq  (translate
          (fun s : state =>
           exists statePre : var -> value,
             eval_expr s e <> 0 /\
             inv s /\
             (forall x : var, ~ In x l -> s x = statePre x) /\ pre statePre)
          stmt ).
          
  intros stmtBT spB annexB transEq.
  rewrite transEq in ih1.
  
  caseEq (   wp_stmt stmtBT
            (fun s : state =>
             exists statePre : var -> value,
               inv s /\
               (forall x : var, ~ In x l -> s x = statePre x) /\ pre statePre) ).

   intros wpBody annexBody wpBodyEq.
      
   rewrite wpBodyEq in ih1.
     
   caseEq (
       wp_stmt
            (While e
            (Inv
            (fun s : state =>
             exists statePre : var -> value,
               inv s /\
               (forall x : var, ~ In x l -> s x = statePre x) /\ pre statePre)
            nil) stmtBT) post
  ).
  intros wpWhile annexWhile wpEq.
  simpl in wpEq.
  rewrite wpBodyEq in wpEq.
  injection wpEq.
  intros wpAnnexEq.
  intros wpWhileEq.
  intros conditions .
  destruct conditions as (sp_impl_post, annexSpH). 
  rewrite <- wpWhileEq.
  
  
(*  subst wpWhile.*)
  assert ( pre_impl_newInv:= allIn_P_list_impl_head_list _ _ annexSpH).
  assert ( spBody_impl_newInv := allIn_P_list_impl_head_list _ _ (allIn_P_list_impl_tail_list _ _  annexSpH)).
  assert ( annexBodyH := allIn_P_list_impl_tail_list _ _ (allIn_P_list_impl_tail_list _ _  annexSpH)).
  clear annexSpH.
  assert (  ih11 := ih1 ( conj spBody_impl_newInv  annexBodyH) ).

  destruct ih11 as ( inv_cond_impl_wpBody , annexBodyHolds).

  split.
  assumption.
  rewrite <- wpAnnexEq.
  intros P annexes.
  simpl in annexes.
  destruct annexes.


  rewrite H.
  clear H.
  intros s H100 H102.
  apply inv_cond_impl_wpBody.
  destruct H102.
  exists x.
  intuition.

  destruct  H.
  rewrite H.
  intros s H100 H102.
  apply sp_impl_post.
  destruct H102.
  exists x.
  intuition.
  apply annexBodyHolds.
  assumption.

  (*seq*)
  assert (ih1 := IHstmt1 pre).
  clear IHstmt1.
  caseEq (  translate pre stmt1).
  intros stmt1T sp1 annex1sp trans1Eq.
  rewrite trans1Eq in ih1.

  assert ( ih2 := IHstmt2 sp1).
  clear IHstmt2.
  caseEq (  translate sp1 stmt2).
  intros stmt2T sp annex2sp trans2Eq.
  rewrite trans2Eq in ih2.

  caseEq (wp_stmt (Sseq stmt1T stmt2T) post ).
  intros wpSeq annexWp wpSeqEq.
  simpl in wpSeqEq.
  caseEq ( wp_stmt stmt2T post).
  
  intros wpst1 annexWpst1 wpst1Eq.
  rewrite wpst1Eq in wpSeqEq.
  
  caseEq ( wp_stmt stmt1T wpst1).
  intros wpst2 annexWpst2 wpst2Eq.
  rewrite wpst2Eq in wpSeqEq.
  
  assert ( ih22 := ih2 post).
  rewrite wpst1Eq in ih22.

  
  assert ( ih11 := ih1 wpst1).
  rewrite wpst2Eq in ih11.
  clear ih1 ih2.
  
  intros conditions.
  destruct conditions as ( sp_impl_post , annexSpH).
  
  simpl in wpSeqEq.
  injection wpSeqEq.
  intros appendEq wpEq.

  
  assert ( annexSt1H :=  InP_appendP_l annex1sp annex2sp annexSpH ).
  assert ( annexSt2H :=  InP_appendP_r annex1sp annex2sp annexSpH ).
  clear annexSpH.
  assert ( ih222 := ih22 ( conj sp_impl_post   annexSt2H) ).
  destruct ih222 as ( sp_impl_wpst1 , annexWpst1H).
  
  assert  ( ih111 := ih11 ( conj sp_impl_wpst1  annexSt1H) ).
  destruct ih111 as (pre_impl_wpst2, annexWpst2H).
  rewrite <- wpEq .
  split.
  assumption.
  rewrite <- appendEq.
  intros.
  apply ( InP_appendP   annexWpst2 annexWpst1 annexWpst2H  annexWpst1H ). 
  assumption.
Qed.
 
(*
Lemma toto : forall ( st : stmt) 
                                 (pre: assertion)  post,
    let (stmtT , SP , annex ) := translate pre st in 
    ( forall s, (pre s -> wp_propag_stmt st post s) ) ->
    ( (forall s, SP s -> post s  )  /\   forall P,  (  InP P annex ) ->   P )  .

 Lemma coco : forall (st: stmt)  
                                    (pre post : assertion) ,
    let (stmtT , SP , annexSP ) := translate pre st in
    let (wp, annexWP) := (wp_stmt stmtT post) in 
    ( (forall s, SP s -> post s )  /\   forall P,  (  InP P annexSP ) ->   P ) ->
    ( ( forall s , pre s -> wp s )  /\   forall P,  (  InP P annexWP ) ->   P ).
*)
Lemma wpPropImplieswpSimpl : forall (st : stmt ) ( pre post : assertion ) ,
let (stmtT , SP , annex ) := translate pre st in 
let (wp, annexWP) := (wp_stmt stmtT post) in 
    ( forall s, (pre s -> wp_propag_stmt st post s) ) ->
 ( ( forall s , pre s -> wp s )  /\   forall P,  (  InP P annexWP ) ->   P ).
Proof.
  intros stmt pre post. 
  simpl...
  caseEq ( translate pre stmt).
  intros stmtT  sp annexSP spEq.
  caseEq ( wp_stmt stmtT post ).
  intros wp annexWp wpEq.
  generalize ( coco stmt  pre post). 
  
  rewrite spEq .
  rewrite wpEq.
  intros spp wpp .

  generalize (toto stmt pre post).
  rewrite spEq .
  tauto. 
Qed.

















 





















