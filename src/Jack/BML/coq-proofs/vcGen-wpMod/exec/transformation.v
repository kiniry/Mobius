Require Import semantique. 
Require Import Ensembles.
Require Import List.
Require Import wp.
Require Import wpMod.
Require Import ZArith.
Require Import Classical.
Axiom user : forall t: Type, t.
(* a function for generating fresh variables *)
Inductive  fresh : list Var -> Var -> Prop := 
|isFresh : forall lVar y  , ~(In y lVar ) -> (fresh lVar y).
   
(* a function  for generating a fresh constant*)
(* Require Import ZArith.
(*defined rapidly *)
Inductive AuxVar : Set := 
AuxName : Var-> Z-> AuxVar. *)

 Inductive stmtJAssume : Set := 
 | SkipAssume : stmtJAssume
 |  AffectAssume : Var -> NumExpr -> stmtJAssume
(* | Assume  : State -> Assertion -> stmtJAssume*)
 | SeqAssume : stmtJAssume -> stmtJAssume -> stmtJAssume 
 | IfAssume : NumExpr -> stmtJAssume  ->  stmtJAssume  -> stmtJAssume  
(*note that the second argument is a list of pairs of prog variables and auxiliary variables, but we do not see the difference as both variables are from the type Var *)
 | WhileAssume : Invariant_j ->  list  ( Var* Var ) ->NumExpr ->  stmtJAssume  ->  stmtJAssume  .

(*operational semantics *)
Inductive execStmtAss : State -> stmtJAssume    -> State -> Set :=
| execSkipAss : forall s, execStmtAss s (SkipAssume ) s
| execAffectAss : forall s v exp  ,   execStmtAss s (AffectAssume  v exp) (update s v (neval s exp))
| exectBsIfTrue: forall s s' cond stThen stElse, 
        neval s cond <> 0 -> execStmtAss s stThen s'  ->
                       execStmtAss s (IfAssume cond stThen stElse) s'
| exectBsIfFalse: forall s s' cond stThen stElse, 
        neval s cond = 0 -> execStmtAss s stElse s'  ->
                       execStmtAss s (IfAssume cond stThen stElse) s'
| execBsWhileFalse: forall inv listSubst  cond  stmt  s, neval s cond = 0 -> 
          execStmtAss s (WhileAssume (inv_j inv)  listSubst  cond  stmt) s
| execBsWhileTrue: forall inv   listSubst cond stmt   s s' s'', 
          neval s cond <> 0 -> 
          (execStmtAss s stmt s') -> 
          (execStmtAss s' (WhileAssume   (inv_j inv) listSubst  cond   stmt) s'') ->
          (execStmtAss s  (WhileAssume   (inv_j inv) listSubst  cond   stmt) s'')
| execBsSeq: forall s s' s'' st1 st2, execStmtAss s st1 s' -> execStmtAss s' st2 s'' -> execStmtAss s (SeqAssume st1 st2) s''.

(*constructing a  new auxiliary variable corresponding to the value of the variable given as first parameter at program state given as second parameter *)
Inductive constructModVarSubstList : list Var -> Z ->  State -> list (Var *Var) -> Set := 
 | empty : forall lVar   z state   lVarSubst , lVar = nil -> lVarSubst = nil ->  ( constructModVarSubstList lVar z state lVarSubst)
 | notEmpty : forall lVar   z ( lVarHead : Var)  lVarTail state lVarSubst lVarSubstHead lVarSubstTail,
          lVar = lVarHead :: lVarTail -> 
	  lVarSubst = lVarSubstHead :: lVarSubstTail ->
          lVarSubstHead = ( lVarHead ,  ( AuxName lVarHead z ) )   -> 
	  ( constructModVarSubstList lVarTail z  state lVarSubstTail) -> 
	  ( constructModVarSubstList lVar z  state lVarSubst ).


Inductive sp :  myProp * State * Z * stmt_m -> stmtJAssume * myProp  * State * Z -> Prop := 
   | isSpSkip : forall state z ass, sp  (ass,state, z, Skip Invariant_m)  (SkipAssume,  ass,  state,  z)
   | isSpAssign : forall var expr  ass state z , 
                            sp (ass, state, z, Affect Invariant_m var expr) (AffectAssume var expr, ass, update state var (neval  state expr), z)
   | isSpSeq : forall  st1 st2 ass state ass1 state1 ass2 state2 st1j st2j z z1 z2 , 
                            ( sp    (ass  , state   , z  , st1  )       (st1j, ass1,  state1 , z1) ) ->
                            ( sp    (ass1, state1, z1, st2  ) (  st2j, ass2, state2, z2) ) -> 
                            ( sp    (ass, state, z, (Seq Invariant_m st1 st2) ) ( ( SeqAssume st1j st2j ), ass2, state2 , z2  ))
   | isSpIf : forall   expB st1 st2 ass state assT assF  stateT stateF st2j st1j z zt ze, 
                            (sp  (  ( p_and  ( p_neq  ( neval state  expB  )  0 ) ass   ), state, z , st1 )   (  st1j, assT, stateT , zt  ) ) ->
                            (sp  (  ( p_and   ( p_eq ( neval state  expB  )  0 )   ass  ), state, zt , st2 )   (  st2j, assF, stateF ,ze) ) ->                       
                            let stateMerge := fun v: Var => if ( Zeq  ( neval state  expB  )  0 ) 
                                                                                    then (neval stateF (nvar v )) 
                                                                                    else  ( neval stateT (nvar v))  in 
                                   ( sp    ( ass, state, z , ( If Invariant_m expB  st1 st2) )  
                                             (  ( IfAssume expB  st1j   st2j  ),  p_or assF  assT ,  stateMerge, ze  ) )
  | isSpwhile : forall  expB stmt ass state inv lVar stmtj assIter stateIter z zIt lVarSubst,
                            let  stateWithMod := ( fun var: Var =>  
                                                                         if  ( In_dec varEqDec var lVar ) 
                                                                         then (neval state (nvar  ( AuxName var z )) )
                                                                         else  (neval state (nvar var) ) )  in   
                            let z := z + 1 in 
                            (* let assume := (Assume stateWithMod ( fun s: State =>
                                                                 ( p_forallv (fun x: Var =>  
                                                                                 ( p_implies  (p_in  x lVar ) ( p_eq ( neval s  ( nvar x) ) 
                                                                                                                      (stateWithMod x) )))))) in *)
                                                                                                    
                            let newInv :=  (fun s: State => ( p_and (p_and ass  ( inv s ) )  
                                                                                             ( p_forallv ( fun v: Var => (p_implies (p_not ( p_in  v lVar))    
                                                                                                                                        ( p_eq ( neval state (nvar v ) )  ( neval s (nvar v) )))))) 
                                                                                              ) in
                           (evalMyProp ass -> evalMyProp (inv state) ) -> 
                          (*CONSTRUCT THE SUBSTITUTION lIST*)
			  ( constructModVarSubstList lVar z stateWithMod lVarSubst ) -> 
                           (sp (   (p_and (  newInv stateWithMod )  
                                                   ( p_not( p_eq ( neval stateWithMod expB )  0) )) , stateWithMod , z , stmt) (stmtj, assIter, stateIter , zIt ) ) ->
                               ( sp                (    ass, 
                                                          state,     
                                                          z,
                                                          While  Invariant_m expB ( inv_m  inv lVar )  stmt )
                                                    
                                                    ( WhileAssume (inv_j newInv) lVarSubst expB stmtj   , 
                                                       p_and  (  p_and (inv stateWithMod) ass )  
                                                                    (  p_eq ( neval stateWithMod expB )  0) , 
                                                       stateWithMod,  
                                                       zIt ) ).
                                


Inductive wpAssume  :   stmtJAssume -> Assertion -> Assertion -> list Assertion -> Prop:=
| wpSkipAss : forall a,    ( wpAssume  SkipAssume a  a nil )
| wpSeqAss : forall s1 s2 post p2 P2 p1 P1, 
                    ( wpAssume s2 post p2  P2) -> 
                    ( wpAssume s1  p2 p1  P1) ->
                    (wpAssume (SeqAssume  s1 s2) post p1  (P1 ++ P2 ) )
| wpAffectAss: forall a v exp, 
                    ( wpAssume (AffectAssume  v exp)  a   (fun s => a (update s v (neval s exp)))  nil)
| wpIfAss: forall pT PT pF PF post cond thenSt elseSt, 
                    ( wpAssume thenSt post pT PT) -> 
                    ( wpAssume elseSt post pF PF) ->
                    (wpAssume (IfAssume  cond thenSt elseSt )  
                                         post 
                                         ((fun s => p_and ( p_implies (p_neq (neval s cond) 0) (pT s) ) 
                                                                       ( p_implies (p_eq   (neval s cond)  0) (pF s))) )
                                         (PT ++ PF ) )

(*TODO ; apply the substitutions from listModSubst on  Cs Ci Pl *)
| wpWhileAss : forall stmt inv pI PI cond  listModSubst (post  : Assertion),
                 ( wpAssume stmt inv pI PI) -> 
                 let Cs := fun s => (p_implies (p_and  (inv s)  (p_neq (neval s cond) 0))  (pI s)) in
                 let Ci := fun s => (p_implies (p_and (inv s) (p_eq (neval s cond)  0)) (post  s) ) in
                ( wpAssume (WhileAssume  (inv_j inv)  listModSubst cond stmt )  post inv  ( Cs :: Ci ::  PI ) ).

(* the axiom (which must be  a lemma ) says that  sp returns closed formulas *)
 Axiom spClosed :  forall stmtm stmtj Pre Post zPre zPost statePre statePost ,
(sp ( Pre , statePre , zPre , stmtm ) ( stmtj , Post , statePost, zPost ))  -> 
forall state , ( fun s : State => Post ) state = Post . 

Lemma spStrongerThanPre : forall stmtm  stmtj Pre Post zPre zPost statePre statePost , 
 (sp (Pre , statePre , zPre , stmtm) ( stmtj , Post , statePost,  zPost )) -> ( (evalMyProp Post )->  (evalMyProp Pre ) ).
 Proof with auto.
 intros stmtM; induction stmtM; intros until statePost; intros Hsp Hpost.
inversion Hsp; subst...
inversion Hsp; subst...
inversion Hsp; subst...
simpl in Hpost.
destruct Hpost.
eassert(Hfalse := (IHstmtM2 _ _ _ _ _ _ _ H10 H)).
simpl in Hfalse; destruct Hfalse...
eassert(Htrue := (IHstmtM1 _ _ _ _ _ _ _ H1 H)).
simpl in Htrue; destruct Htrue...

(* while *)
inversion Hsp. 
unfold stateWithMod in H1, H7, H8, H10, H11, H; 
clear stateWithMod; subst...
eassert(Hs := (IHstmtM _ _ _ _ _ _ _ H11 ))...
simpl in Hpost.
simpl in Hs.
destruct Hpost as [[Hpost1 Hpost2] Hpost3]...

(* seq *)
inversion Hsp; subst...
eassert(Hs1 := (IHstmtM1 _ _ _ _ _ _ _ H1 )).
eassert(Hs2 := (IHstmtM2 _ _ _ _ _ _ _ H9 ))...
Qed.
 




(*CLOSED PREDICATES IN POST CAN BE TAKEN OUT WHEN APPLIED TO A WP FUNCTION *)
(* p CLOSED ,  WP(ST, p /\ Q) = WP(ST,Q) /\ p*)
Axiom closedPredinPost :  forall stmt Pre1 PreL1 Pre2 PreL2 (Post1 Post2 : Assertion ) (prop : myProp),  
(forall state, (Post2 state ) = prop ) ->
(wpAssume stmt ( fun s : State => p_and (Post1 s)  (  Post2 s)  ) Pre1 PreL1 )  ->   
(wpAssume stmt Post1 Pre2 PreL2 ) /\ (evalMyProp  prop) .


  
(*sp ( stmt, pre) = post   ->  (post ->  pre) , PROVED BY JULIEN     *)
(*used in the case of a sequence*)
(* Axiom spStrongerThanPre : forall stmtm  stmtj Pre Post zPre zPost statePre statePost , 
 (sp (Pre , statePre , zPre , stmtm) ( stmtj , Post , statePost,  zPost )) -> ( (evalMyProp Post )->  (evalMyProp Pre ) ).
*)

(*RELATION WP AND SP *)
(* ( P -> WP(ST, Q) ) -> (Q -> SP (ST, P)) *)
Axiom relWpSp : forall stmtM stmtJ WP Pre Post SP zPre zPost statePre statePost ,
( is_wpMod  stmtM Post  WP ) ->
                    ( (evalMyProp ( Pre  statePre)) -> ( evalMyProp ( WP  statePre)) ) ->
 (sp  ( (Pre statePre) , statePre, zPre, stmtM   ) (  stmtJ, SP ,  statePost,zPost  )) ->    
((evalMyProp SP ) ->  (evalMyProp  (Post statePost) )).

(*
Proof with auto.
intro stmtM. induction stmtM; intros until statePost; intro hypWP; intro hypWP_Implied; intro hypSP.
(*skip*)
intros SPholds.
inversion hypWP; subst...
inversion hypSP; subst...

(*assign*)

intros SPholds.
inversion hypWP; subst...
inversion hypSP; subst...

(* if *)
intros SPholds.
inversion hypWP; subst...
inversion hypSP; subst...
simpl in *.

assert ( HypWpThen : (  neval statePre n <> 0 /\ evalMyProp (Pre statePre)  )-> evalMyProp (pre_t statePre) ).
intros.
destruct H.
assert ( hypWpImp := hypWP_Implied H0 ).
destruct hypWpImp.
assert (hypWpImp1 := H2 H ).
exact hypWpImp1.
assert (    spBeta : sp
    ((fun s : State => p_and (p_neq (neval s n) 0) (Pre s)) statePre,
    statePre, zPre, stmtM1) (st1j, assT, stateT, zPost)  ).
eassert (hypIndThen := ( IHstmtM1 st1j   pre_t  ( fun s => (  p_and (p_neq (neval s n)  0 )  ( Pre s)  )) Post assT zPre zPost statePre stateT  H5 HypWpThen H1 ) ).
Qed.
*)

Lemma  wpModMon : forall stmtM  Post1 Post2 Pre1 Pre2 ,
(is_wpMod stmtM Post1 Pre1) ->  
(is_wpMod stmtM Post2 Pre2) -> 
 ( forall st , (evalMyProp (Post1 st) ) -> (evalMyProp (Post2 st)) )   ->  
(forall st, ( (evalMyProp (Pre1 st) ) -> (evalMyProp (Pre2 st))) )   .

Proof with auto.
intro stmtM. induction stmtM; intros until Pre2; intro wpMod1; intro wpMod2.
(*skip*)
inversion wpMod1; subst...
inversion wpMod2; subst...

(*assign*)
intros.
inversion wpMod1; subst...
inversion wpMod2; subst...
assert ( instantiateH := H ( update st v (neval st n) ) ).
unfold update_assert in *.
assert ( hypIdenticToGoal := instantiateH H0).
exact hypIdenticToGoal.

(*if *)
intros.
inversion wpMod1; subst...
inversion wpMod2; subst...
assert (hypIndThen := IHstmtM1 Post1 Post2   pre_t  pre_t0 H7 H9 ).
assert (hypIndElse := IHstmtM2 Post1 Post2   pre_f  pre_f0 H6 H8 ).
simpl...
simpl in *.
split.
intros.
assert (hypThen := hypIndThen H ).
destruct H0.
assert ( trueCase := H0 H1 ).
assert ( hypThen1 := hypThen st trueCase ).
exact hypThen1.

intros.
assert (hypElse := hypIndElse H).
destruct H0.
assert (falseCase := H2 H1 ).
assert (hypElse1 := hypElse st falseCase).
exact hypElse1.



(*While*)
intros.
inversion wpMod1; subst...
inversion wpMod2; subst...
simpl in *.
split.

destruct  H0 as [ inv [ inv_Preserv inv_Impl_Post ]] ;  exact inv.
split.
intros.
destruct  H0 as [ inv [ inv_Impl_Post  inv_Preserv ]] .
assert ( inv_Impl_Post1 := inv_Impl_Post st0  H1 H2 H3).
assert ( hypIdentGoal := H st0 inv_Impl_Post1).
exact hypIdentGoal.
intros.
assert ( invImpliesInv :  forall st , 
 (evalMyProp ( ( fun stf : State =>
     p_foralls
       (fun st : State =>
        p_and
          (p_forallv
             (fun x : Var =>
              p_implies (p_not (p_in x lVar)) (p_eq (stf x) (st x))))
          (invariant stf)) ) st ) )   ->  
 (evalMyProp ( ( fun stf : State =>
     p_foralls
       (fun st : State =>
        p_and
          (p_forallv
             (fun x : Var =>
              p_implies (p_not (p_in x lVar)) (p_eq (stf x) (st x))))
          (invariant stf)) ) st) )
  ).
intros.
exact H4.
eassert ( hypInd := ( IHstmtM _ _ _ _ H6 H8 invImpliesInv )  ).
assert (hypInd1 := hypInd st0).
destruct  H0 as [ inv [ inv_Impl_Post  inv_Preserv ]] .
assert (hypInvPreserv := inv_Preserv st0 H1 H2 H3 ).
assert (hypIdentGoal := hypInd1 hypInvPreserv).
exact hypIdentGoal.

(*Sequence *)
intros.
inversion wpMod1; subst...
inversion wpMod2; subst...
assert ( hypInd2 := IHstmtM2 Post1 Post2 pre_st2 pre_st0 H3 H4 H).
assert ( hypInd1 := IHstmtM1 pre_st2 pre_st0 Pre1 Pre2 H6 H8 hypInd2).
assert (hypIdentGoal := hypInd1 st H0).
exact hypIdentGoal.
Qed.


Axiom wpModTotal: forall stmtM Post, exists Pre,  (is_wpMod stmtM Post Pre).


Lemma Pre_implies_wp_of_sp : forall stmtM stmtJ PRE  sPost  zPre zPost statePre statePost wPre , 
  ( sp ( ( PRE  statePre ) , statePre , zPre, stmtM) ( stmtJ,  sPost , statePost, zPost ) )->  
  ( is_wpMod  stmtM ( fun s =>  sPost)  wPre ) -> 
  ( (evalMyProp ( PRE  statePre)) -> ( evalMyProp ( wPre  statePre) ) ) .

Proof with auto.
intro stmtM. induction stmtM; intros until wPre; intro SP;  intro WP.

(*skip *) 
intros .
inversion WP; subst ...
inversion SP; subst ... 

(*assign*)
intros.
inversion WP; subst ...
inversion SP; subst ... 


(*if*)
intros .
inversion SP ; subst ... 
inversion WP; subst ...

simpl in *.
split.
intros.

(*then case *)
assert ( existsWpThen := wpModTotal  stmtM1 (fun s  => assT)  ).
elim existsWpThen. 
intro wpExists. 
intros.

eassert ( IHypThen1 :=  (IHstmtM1 st1j ( fun s =>   p_and (p_neq (neval statePre n) 0) (PRE statePre) )   assT zPre zt statePre stateT wpExists _ H1)).
exact H2.

assert ( Then_impl_ThenOrElse :  ( evalMyProp assT ) -> (  evalMyProp (  p_or assF assT) )    ).
intros.
simpl in *.
right. 
exact H3.
eassert ( applyMonotThenInStatePre := ( wpModMon  stmtM1  ( fun s => assT) (fun s => (  p_or assF assT)  ) wpExists pre_t H1 H7  _  statePre ) ).
intro State.
assumption.
simpl in *.

assert (PandCond := conj H0 H).
assert ( assWpExists := IHypThen1  PandCond ).
assert ( goal :=  applyMonotThenInStatePre assWpExists  ).
assumption.

(*else case *)
assert ( existsWpElse := wpModTotal  stmtM2 (fun s  => assF)  ).
elim existsWpElse. 
intro wpExists. 
intros.

eassert ( IHypElse1 :=  (IHstmtM2 st2j ( fun s =>   p_and (p_eq (neval statePre n) 0) (PRE statePre) )   assF zt zPost statePre stateF wpExists _  H0)).
exact H11.

assert ( Then_impl_ThenOrElse :  ( evalMyProp assF ) -> (  evalMyProp (  p_or assF assT) )    ).
intros.
simpl in *.
left. 
exact H3.
eassert ( applyMonotElseInStatePre := ( wpModMon  stmtM2  ( fun s => assF) (fun s => (  p_or assF assT)  ) wpExists pre_f H0 H6  _  statePre ) ).
intro State.
assumption.
simpl in *.

assert (PandNotCond := conj H1 H).
assert ( assWpExists := IHypElse1  PandNotCond ).
assert ( goal :=  applyMonotElseInStatePre assWpExists  ).
assumption.


(*while *)

intros .
inversion SP ; subst ... 
inversion WP; subst ...
simpl in *.
split.

(*the invariant is proven *)
assert ( goal := H3 H). 
assumption.


(*the invariant preservation*)
simpl in *.
split.
intros .
split.
split.
Focus 2.
assumption.
assert (invInStatePre := conj H1 H0).
Focus 3.
intros .




















(*version Benjamin *)
 (* Lemma wpModImplieswp : forall stmtM  P Q  Q1 preM preJ listPogJ  stmtJ (assPost : myProp)  statePre  stateSP  zPre zPost,
                    ( is_wpMod  stmtM Q  preM ) ->
                    ( (evalMyProp ( P  statePre)) -> ( evalMyProp ( preM  statePre)) ) ->
                   (sp  ( (P statePre) , statePre, zPre, stmtM   ) (  stmtJ, assPost ,  stateSP,zPost  ) ) ->   
                   ( ( evalMyProp ( Q  stateSP ) ) ->  ( evalMyProp ( Q1  stateSP ) ) ) ->
                   (wpAssume stmtJ Q1   preJ listPogJ )  -> 
                                  ((evalMyProp ( preM statePre)  -> ( evalMyProp ( preJ statePre)) )  /\ 
                                         (forall s, (forall f: Assertion, (In f listPogJ) -> ( evalMyProp (f s)   )))).
*)

 Lemma wpModImplieswp : forall stmtM  P Q  Q1 preM preJ listPogJ  stmtJ (assPost : myProp)  statePre  stateSP  zPre zPost,
                    ( is_wpMod  stmtM Q  preM ) ->
                    ( (evalMyProp ( P  statePre)) -> ( evalMyProp ( preM  statePre)) ) ->
                   (sp  ( (P statePre) , statePre, zPre, stmtM   ) (  stmtJ, assPost ,  stateSP,zPost  ) ) ->   
                   ( ( evalMyProp ( Q  stateSP ) ) ->  ( evalMyProp ( Q1  stateSP ) ) ) ->
                   (wpAssume stmtJ Q1   preJ listPogJ )  -> 
                                  ((evalMyProp ( P statePre)  -> ( evalMyProp ( preJ statePre)) )  /\ 
                                         (forall s, (forall f: Assertion, (In f listPogJ) -> ( evalMyProp (f s)   )))).

Proof with  auto.


intro stmtM.
induction stmtM; intros until zPost; intros HwpMod Himply Hsp HpostRelation HwpAssume. 

(* While *)
Focus  4.

inversion Hsp.  
unfold newInv in *.
subst.
simpl ...
inversion HwpMod; subst...

inversion HwpAssume; 
simpl in *;

unfold Cs in *; clear Cs.
unfold Ci in *; clear Ci.
subst...

simpl ...
split...
intros state vc h.
destruct h as [  vcPreserv | [   vcTermination | vcBody ]].

Focus 2. 
subst ...
simpl ...

intros .
destruct H as [ [ P_in_statePre invHolds  ]  varNotMod]. 
assert ( Himply1 := Himply )


(* skip *)
inversion HwpMod; subst...
inversion Hsp; subst ...
inversion HwpAssume; subst ...
split.
intros;assumption.
intros s f absurde;
inversion absurde.

(* affect *)
inversion HwpMod; subst...
inversion Hsp; subst ...
inversion HwpAssume; subst ...
split.
unfold update_assert.
intros; assumption.
intros s f absurde;
inversion absurde.


(* If *)

inversion HwpMod; subst...
inversion Hsp; subst ...
inversion HwpAssume; subst ...

 assert (hypPandCimplPreT :  ( evalMyProp ((fun s : State => p_and (p_neq (neval statePre n) 0) (P s) ) statePre ) ) -> ( evalMyProp ( pre_t statePre ) )  ).
(*debut assert *)
intros Hyp_PandCond.
simpl in Hyp_PandCond.
simpl in Himply.
destruct Hyp_PandCond .
assert ( hyp_NimplPre_t := Himply H0 ).
destruct hyp_NimplPre_t.
assert(hyp_Pre_t := H2 H).
exact hyp_Pre_t.
(* fin assert*)

eassert ( HypIndThen := (IHstmtM1  _ Q pre_t pT PT st1j  assT statePre   stateT zPre zt H5  hypPandCimplPreT H1    H8 )) .

assert (hypPandNotCimplPreF :  ( evalMyProp ((fun s : State => p_and (p_eq (neval statePre n) 0) (P s) ) statePre ) ) -> ( evalMyProp ( pre_f statePre ) )  ).
(* debut preuve assert *)
simpl.
intros [Hf Hp].
simpl in Himply.
assert ( h := Himply Hp ).
destruct h as [Hpre_t Hpre_f].
exact (Hpre_f Hf).
(* fin preuve assert *)

assert ( HypIndElse := (IHstmtM2  (*(fun s : State => p_and (p_eq (neval statePre n) 0) (P s) )*)  _ Q pre_f pF PF st2j  assF statePre stateF zt zPost H4 hypPandNotCimplPreF H12 H9 )) .
simpl in HypIndThen .
simpl in HypIndElse.
destruct HypIndThen as [HThenPre HThenVc].
destruct HypIndElse as [HElsePre HElseVc].
split.
(* preuve des pres *)
intro.
simpl in *.
destruct H as [hThen hElse].
split;
intro...
(* fin preuve pres *)

(* preuve vcs *)
intros s f h.
assert(h1 :=  in_app_or _ _ _ h).
destruct h1...
(*fin preuve vcs *)



(*Sequence*)
inversion HwpMod; subst...
inversion Hsp; subst ...
inversion HwpAssume; subst ...
eassert ( HrelWpSpS1 := (relWpSp _ _ _ _ _ _ _ _ _ _ H4 _ H2) )...

eassert(HindS2 := (IHstmtM2 (fun _ => ass1) Q pre_st2 p2 P2 st2j assPost state1 stateSP z1 zPost _ _ _ _))...
assert(Htotale :=wpModTotalstmtM1 p2).
elim Htotale...
intros x hx. 
destruct HindS2 as [HindS2a HindS2b].

eassert(HindS1 := (IHstmtM1 P p2  x  preJ P1 st1j ass1 statePre state1 zPre z1 _ _ _ _))...
eassert ( wpUseMonotone := (wpModMon _ _ _ _ _ state1  H4 hx))...
eassert ( wpUseMonotone := (wpModMon _ _ _ _ _ state1  H4 hx))...
destruct HindS1 as [HindS1a HindS1b].
split...
intros s f h.
assert(h1 :=  in_app_or _ _ _ h).
destruct h1...



Qed.