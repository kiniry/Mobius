Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Require Import BasicDef.
Require Import Logic_n.
Require Import Language.
Require Import Semantic.
Require Import Wp_propag.
Require Import Classical.
Require Import axioms.


Lemma PropInPost : forall (pre : assertion ) stmt,
   forall p post s' , (forall s ,  pre  s' /\ p s -> wp_propag_stmt stmt post s ) ->
   (forall s , pre s'  /\ p s -> wp_propag_stmt stmt  ( fun state => post state /\ pre s' ) s ). 
Proof.
  intros pre  stmt; induction stmt; simpl; auto.
  (*assign*)
  intros p post s' pre_wp s prec.
  split. 
  apply pre_wp. 
  assumption.
  destruct prec.
  assumption.

  (* if *) 
  intros p post  s' pre_impl_wp s prec. 
 
  split.
  intros.
  apply ( IHstmt1 ( fun s =>  p s /\ eval_expr s e <> 0 ) ). 
  intros s0 prec0.
  destruct prec0 as (pre_s0 , ( p_s0, cond_s0)).
  assert ( pre_and_p := conj pre_s0  p_s0). 
  assert ( pre_wp1 := pre_impl_wp s0 ). 
  assert ( pre_wp2 := pre_wp1 pre_and_p).
  destruct pre_wp2 as (tH, fH).
  apply tH.
  assumption.
  intuition.

  intros.
  apply ( IHstmt2 ( fun s =>  p s /\ eval_expr s e = 0 ) ). 
  intros s0 prec0.
  destruct prec0 as (pre_s0 , ( p_s0, cond_s0)).
  assert ( pre_and_p := conj pre_s0  p_s0). 
  assert ( pre_wp1 := pre_impl_wp s0 ). 
  assert ( pre_wp2 := pre_wp1 pre_and_p).
  destruct pre_wp2 as (tH, fH).
  apply fH.
  assumption.
  intuition.

  (*while*)
  destruct i as ( inv , modi).
  intros p post s' pre_imp_wp.
  intros s. 
  intros pre_inv.
  assert ( pre_wp1 := pre_imp_wp s pre_inv ).
  intuition. 
  intros p post  s' pre_impl_post  pre_p_s' .
  split.
  apply pre_impl_post.
  assumption.
  intuition.

  (*seq*)
  intros p post s' pre_post. 
  assert  ( HypInd1 := IHstmt1  p ( wp_propag_stmt stmt2 post) s' pre_post ) . 
  assert ( Hyp2 : forall s , pre s'  /\ ( wp_propag_stmt stmt2 post) s -> ( wp_propag_stmt stmt2 post) s ).
  intros. 
  intuition.
  assert ( HypInd2 := IHstmt2   ( wp_propag_stmt stmt2 post) post s' Hyp2 ).
  assert ( HypInd3 : forall s , wp_propag_stmt stmt2 post s /\ pre s' ->                 
                                  ( wp_propag_stmt stmt2   (fun state => post state /\ pre s' ) ) s ).
  intros.
  apply HypInd2.
  intuition. 
  assert ( HypMon3:=  wp_monotone  
                                      stmt1
                                      ( fun s =>   ( wp_propag_stmt stmt2 post) s /\ pre s'   )
                                      ( fun s => ( wp_propag_stmt stmt2 (fun state => post state /\ pre s' )) s )
                                      ).
  simpl in *.
  assert ( HypInd5:= HypMon3 HypInd3).
  intros  s prec.
  assert (etaExpH := etaExp
                                    _ 
                                    _  
                                    ( wp_propag_stmt stmt2 (fun state : state => post state /\ pre s' ) )
                                    ).
  assert (ext := extentionalType _ _ _ _  etaExpH).
  clear etaExpH.
  rewrite  ext in HypInd5.
  apply HypInd5.
  apply HypInd1.
  assumption.
Qed. 









Lemma univToEx: forall stmt (Pre1 Pre2 Post : assertion) lVar,
  ( forall s1 s2,  ( (Pre1 s1 /\ Pre2 s2 /\ ( forall x, ~ In x lVar  -> s2 x = s1 x  ) )  ->  wp_propag_stmt stmt Post s2 ) )   ->
  ( forall s2 , (exists s1, Pre1 s1 /\  Pre2 s2 /\ ( forall x, ~ In x lVar  -> s2 x = s1 x  ) ) -> wp_propag_stmt stmt Post s2  ).

Proof.
  induction stmt; intros Pre1 Pre2 Post lVar ; simpl ; auto;
  intros Pre_impl_Post s2 ex_s1;  elim ex_s1;
  intros x Pre_x.

  (*assign*)    
  apply ( Pre_impl_Post   x s2) .
  assumption.

  (*if*)
  split.
  intros cond.
  apply ( IHstmt1 Pre1 ( fun s => Pre2 s /\ eval_expr s e <> 0) Post lVar ) .
  intros s3 s1 precond.
  destruct precond as (Pre1_s1 , (( Pre2_s3, cond_s3) , modif) ). 
  assert ( H1 := Pre_impl_Post  s3 s1 (  conj Pre1_s1 (conj Pre2_s3 modif))). 
  destruct H1 as (H1, H2 ).
  apply H1.
  assumption.
  exists x. 
  intuition. 

  intros cond.
  apply ( IHstmt2 Pre1 ( fun s => Pre2 s /\ eval_expr s e = 0) Post lVar) .
  intros s3 s1 precond.
  destruct precond as (Pre1_s1 , (( Pre2_s3, cond_s3) , modif) ). 
  assert ( H1 := Pre_impl_Post  s3 s1 (  conj Pre1_s1 (conj Pre2_s3 modif))). 

  destruct H1 as (H1, H2 ).
  apply H2.
  assumption.
  exists x. 
  intuition. 

  (* while *)
  destruct i as ( inv, modi). 
  destruct (Pre_impl_Post x s2 Pre_x)  as ( inv_s2 , ( pres, inv_post)).
  repeat split.  
  assumption.
  intros s' cond_s' inv_s' mod_s'.
  apply pres.
  assumption.
  assumption.
  assumption.
  intros s' notCond_s' inv_s' mod_s'. 
  apply inv_post.
  assumption.
  assumption.
  assumption.
  apply ( Pre_impl_Post x s2).
  assumption.

  (*seq*)
  apply (IHstmt1 Pre1 Pre2 (wp_propag_stmt stmt2 Post ) lVar).
  intros s3 s1 prec. 
  apply ( Pre_impl_Post s3 s1) .
  assumption.
  exists x.
  assumption.
Qed.


Lemma existsInPost1 : forall stmt (P1 P2 : assertion) lVar   ,
   forall  ( sPost sPre : state), 
     (wp_propag_stmt stmt  ( fun s => P1 s /\ ( forall x , ~ In x lVar -> s x = sPost x) /\  P2 sPost) sPre ) ->
     (wp_propag_stmt stmt  ( fun s => exists state, P1 s /\  ( forall x , ~ In x lVar -> s x = state x) /\ P2 state) sPre ). 
Proof.
  induction stmt; simpl;auto; intros P1 P2 lVar sPost sPre wp1.

  (*assign*)
  exists sPost.
  assumption.
  
  (*if*)
  destruct wp1 as (bT , bF ).
  split.
  intros.
  apply ( IHstmt1 P1 P2 lVar sPost sPre).
  apply bT.
  assumption.
  intros.
  apply ( IHstmt2 P1 P2 lVar sPost sPre).
  apply bF.
  assumption.

  (*while*)
  destruct i as ( inv, modi).
  destruct wp1 as ( inv_s' , ( pres, post)).
  repeat split.   
  assumption.
  assumption.

  intros s' H1 H2 H3.
  exists sPost. 
  apply post. 
  assumption.
  assumption.
  assumption.
  exists sPost.
  assumption.

  (*seq*)
  assert (IH2 := IHstmt2 P1 P2 lVar sPost  ).
  assert ( H3 := wp_monotone stmt1  _  _ IH2).
  apply (H3 sPre wp1).
Qed.     

 

Lemma existsInPost : forall stmt (P1 P2 : assertion)  ,
   forall sPost sPre , 
     (wp_propag_stmt stmt  ( fun s => P1 s /\ P2 sPost) sPre ) ->
     (wp_propag_stmt stmt  ( fun s => exists state, P1 s /\ P2 state) sPre ). 
Proof.
  induction stmt; simpl;auto; intros P1 P2 sPost sPre wp1.

  (*assign*)
  exists sPost.
  assumption.
  
  (*if*)
  destruct wp1 as (bT , bF ).
  split.
  intros.
  apply ( IHstmt1 P1 P2 sPost sPre).
  apply bT.
  assumption.
  intros.
  apply ( IHstmt2 P1 P2 sPost sPre).
  apply bF.
  assumption.

  (*while*)
  destruct i as ( inv, modi).
  destruct wp1 as ( inv_s' , ( pres, post)).
  repeat split.   
  assumption.
  assumption.

  intros s' H1 H2 H3.
  exists sPost. 
  apply post. 
  assumption.
  assumption.
  assumption.
  exists sPost.
  assumption.

  (*seq*)
  assert (IH2 := IHstmt2 P1 P2 sPost  ).
  assert ( H3 := wp_monotone stmt1  _  _ IH2).
  apply (H3 sPre wp1).
Qed.     



Lemma PropOutOfWp : forall stmt (  P2 Q Post : assertion)  lMod ,
  ( forall ( st2 st1 : state) , 
      Q st1 /\  (forall x : var, ~ In x lMod -> st1 x = st2 x) /\ P2 st2 -> 
      ( wp_propag_stmt stmt ( fun s : state =>
                                                     Post s /\  
                                                     (forall x : var, ~ In x lMod -> s x = st2 x) /\ 
                                                     P2 st2 ) )   st1 ) ->
  ( forall ( st2 st1 : state) , 
      Q st1 /\  (forall x : var, ~ In x lMod -> st1 x = st2 x) /\ P2 st2 -> 
      ( wp_propag_stmt stmt Post ) st1   /\  
      (forall x : var, ~ In x lMod -> st1 x = st2 x) /\ 
      P2 st2 ). 

Proof.
  induction stmt; simpl; auto;
  intros  P2 Q Post lMod wp1 st2 st1 cond.
  (*assign*)
  assert (wp2 := wp1 st2 st1 cond).
  intuition.
 
  (*if *)
  assert (HHH : 
      ( forall (st2 : state) (st1 : var -> value),
            (Q st1 /\ eval_expr st1 e <> 0) /\ 
            (forall x : var, ~ In x lMod -> st1 x = st2 x) /\ 
                 P2 st2 ->
                 wp_propag_stmt stmt1
                 (fun s : state =>
                 Post s /\ (forall x : var, ~ In x lMod -> s x = st2 x) /\ P2 st2)
                 st1)  /\
      ( forall (st2 : state) (st1 : var -> value),
            (Q st1 /\  eval_expr st1 e = 0) /\  
            (forall x : var, ~ In x lMod -> st1 x = st2 x) /\ 
                 P2 st2->
                 wp_propag_stmt stmt2
                 (fun s : state =>
                 Post s /\ (forall x : var, ~ In x lMod -> s x = st2 x) /\ P2 st2)
                 st1)).
      split.

      intros st3 st4 condT.
      destruct condT as ( ( Q_st3, cond_st3) , (modif_st4, P2_st4)).
      destruct (wp1 st3 st4 ( conj Q_st3 ( conj modif_st4 P2_st4))) as ( bT,  bF).
      apply bT.
      assumption.

       intros st3 st4 condT.
      destruct condT as ( ( Q_st3, cond_st3) , (modif_st4, P2_st4)).
      destruct (wp1 st3 st4 ( conj Q_st3 ( conj modif_st4 P2_st4))) as ( bT,  bF).
      apply bF.
      assumption.
      destruct HHH as ( bT, bF).
      destruct cond as ( Q_st1, ( modif_st2, P2_st2)).
      (*start proving the goals *)
      repeat split.

      intros.
      assert (IH1:= IHstmt1 P2 ( fun st1 => Q st1 /\ eval_expr st1 e <> 0)Post lMod bT  st2 st1 ).
      simpl in IH1.
      assert ( IH11 := IH1 ( conj (conj Q_st1 H )  (conj modif_st2 P2_st2 )  )) .
      intuition.

       intros.
      assert (IH1:= IHstmt2 
                             P2 
                             ( fun st1 => Q st1 /\ eval_expr st1 e = 0) 
                             Post 
                             lMod 
                             bF  
                             st2 
                             st1 ).
      simpl in IH1.
      assert ( IH11 := IH1 ( conj (conj Q_st1 H )  (conj modif_st2 P2_st2 )  )) .
      intuition.

     assumption.
     assumption.


   (*while*)
   destruct  i as (inv, modi).
   destruct (wp1 st2 st1 cond ) as ( inv_st1 , ( pres, post)).
   repeat split.
   assumption.
   assumption.
   intros s' notCond inv_s' modif_s'.
   assert(post1:= post s' notCond inv_s'  modif_s').
   intuition.
   intuition.
   intuition.
   
   (*seq*)
   repeat split.
   assert (wp2 := wp1 st2 st1).
   clear wp1.
   assert ( wpConj := wpConjunctive
                                    stmt2  
                                    Post  
                                    ( fun s => (forall x : var, ~ In x lMod -> s x = st2 x) /\ P2 st2 ) ).
   simpl in wpConj.
   rewrite wpConj in wp2.
   clear wpConj.
   assert ( wpConj := wpConjunctive
                                    stmt1  
                                    ( wp_propag_stmt stmt2 (fun s0 : state => Post s0) )
                                    ( wp_propag_stmt stmt2
                                     (fun s0 : state =>
                                     (forall x : var, ~ In x lMod -> s0 x = st2 x) /\ P2 st2) )
                                 ).
     simpl in wpConj.                            
     rewrite wpConj in wp2.
     clear wpConj.
     assert ( wp3 := wp2 cond).
     simpl in wp3.
     rewrite (  etaExpansion _ _  Post ) in wp3.
     rewrite (  etaExpansion _ _  (   wp_propag_stmt stmt2 Post )) in wp3.
     intuition.
     intuition.
     intuition.
Qed.

