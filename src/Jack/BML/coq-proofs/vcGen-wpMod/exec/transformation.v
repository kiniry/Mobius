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
                                                                                                    
                            let newInv :=  (fun s: State => ( p_and ( 
                                                                                       p_and (inv s )  
                                                                                             ( p_forallv ( fun v: Var => (p_implies (p_not ( p_in  v lVar))    
                                                                                                                                        ( p_eq ( neval state (nvar v ) )  ( neval s (nvar v) )))))) 
                                                                                             ass  )) in
                           (evalMyProp ass -> evalMyProp (inv state) ) -> 
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
| wpSeqAss : forall s1 s2 a p2 P2 p1 P1, 
                    ( wpAssume s2 a p2  P2) -> ( wpAssume s1  p2 p1  P1) ->
                                         (wpAssume (SeqAssume  s1 s2) a p1  (P1 ++ P2 ) )
| wpAffectAss: forall a v exp, 
                    ( wpAssume (AffectAssume  v exp)  a   (fun s => a (update s v (neval s exp)))  nil)
| wpIfAss: forall pT PT pF PF a b t f, 
                   ( wpAssume t a pT PT) -> ( wpAssume f a pF PF) ->
                   (wpAssume (IfAssume  b t f)  
                                         a 
                                         ((fun s => p_and ( p_implies (p_neq (neval s b) 0) (pT s) ) 
                                                                       ( p_implies (p_eq (neval s b)  0) (pF s))) )
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
intros stmtM; induction stmtM; intros until statePost; intros Hsp Hpost.
Proof with auto.
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


Lemma spCorrect : forall  stmtJAss state1 state2,
        (execStmtAss  state1 stmtJAss state2) -> 
        forall stmtM    Pre Post z1 z2 , 
         ( sp ( Pre , state1 , z1 , stmtM ) (stmtJAss,  Post , state2, z2 )) ->
         
         ( evalMyProp Pre )  ->
         ( evalMyProp Post   ).
Proof with auto.



intros stmtJ s1 s2 Hexec; induction Hexec; intros until z2; intros Hsp Hpre.

inversion Hsp; subst...
inversion Hsp; subst...

(* if true *)
inversion Hsp; subst...
simpl in H8.
assert(h : forall (a: State), (fun v : Var => a v) = a ).
intros. apply user.
destruct (neval s cond)...
(*destruct but 1: *)
destruct n...
(*destruct but 2: *)
simpl in H8.
simpl.
rewrite h in H8.
rewrite <- H8 in IHHexec.
eassert (HindEx := (IHHexec _ _ _ _ _ H1 _))...
simpl...
(*destruct but 3 *)
simpl in H8.
simpl.
rewrite h in H8.
rewrite <- H8 in IHHexec.
eassert (HindEx := (IHHexec _ _ _ _ _ H1 _))...
simpl...

(* if false *)
inversion Hsp; subst...

simpl.
(* seq *)
inversion Hsp; subst...
apply user.
(* inversion Hexec; subst...
eassert(Hs1 := (IHstmtJ1 _ _ _ _ _ _ _ H1 H5)).
eassert(Hs2 := (IHstmtJ2 _ _ _ _ _ _ _ H9 ))... *)
(* if  *)
apply user. (*
inversion Hsp; subst...
simpl.
inversion Hexec; subst...
destruct (classic ( (neval state1 n)  = 0) ).
destruct H5...
eassert(Htrue := (IHstmtM1 _ _ _ _ _ _ _ H1 _))...
destruct (neval state1 n) ...
destruct H...
simpl in H6...
eassert(Hfalse := (IHstmtM2 _ _ _ _ _ _ _ H10 _ _))...
simpl in H6.
destruct (neval state1 n) ...
destruct H...
simpl in H6...
trivial.
left...

simpl...
*)
apply user.

(* while *)
(* inversion Hsp. 
unfold stateWithMod in H1, H7, H8, H10, H11, H; 
unfold stateWithMod; clear stateWithMod; subst...
unfold newInv in H11, Hsp; clear newInv.
simpl.
eassert(HspStrong1 := (spStrongerThanPre _ _ _ _ _ _ _ _ Hsp )).
eassert(HspStrong2 := (spStrongerThanPre _ _ _ _ _ _ _ _ H11)).
simpl in Hpre.
repeat split...
inversion H1; subst...
Focus 2.
destruct HspStrong2 as [[[h1 h2] h3] h4]; repeat split...
eassert(HindS := (IHstmtM _ _ _ _ _ _ _ H11 ))...
apply HindS.
simpl.
repeat split...
simpl in HspStrong2.

simpl.
repeat split...
eassert(HspStrong1 := (spStrongerThanPre _ _ _ _ _ _ _ _ Hsp )).
eassert(HspStrong2 := (spStrongerThanPre _ _ _ _ _ _ _ _ H11 )).
repeat split...
simpl.
simpl in HspStrong2.
split.
simpl in Hs.
apply user.

*)
(*skip*)
(* intros.
inversion H.
subst ...
*)
(*assignment*)
(* intros.
inversion H. subst ...
*)
(* if case *)
(* intros. 
inversion H.  subst ... *)
apply user.
Qed.
 

(*wp (stmt, P  )*)
Axiom closedPredinPost :  forall stmt Pre1 PreL1 Pre2 PreL2 (Post1 Post2 : Assertion ) (prop : myProp),  
(forall state, (Post2 state ) = prop ) ->
(wpAssume stmt ( fun s : State => p_and (Post1 s)  (  Post2 s)  ) Pre1 PreL1 )  ->   
(wpAssume stmt Post1 Pre2 PreL2 ) /\ (evalMyProp  prop) .

(*sp ( stmt, pre) = post -> (post ->  pre)     *)
(*used in the case of a sequence*)
(* Axiom spStrongerThanPre : forall stmtm  stmtj Pre Post zPre zPost statePre statePost , 
 (sp (Pre , statePre , zPre , stmtm) ( stmtj , Post , statePost,  zPost )) -> ( (evalMyProp Post )->  (evalMyProp Pre ) ).
*)
Axiom relWpSp : forall stmtM stmtJ PreM Pre Post PostJ zPre zPost statePre statePost ,
( is_wpMod  stmtM Post  PreM ) ->
                    ( (evalMyProp ( Pre  statePre)) -> ( evalMyProp ( PreM  statePre)) ) ->
 (sp  ( (Pre statePre) , statePre, zPre, stmtM   ) (  stmtJ, PostJ ,  statePost,zPost  )) ->    
((evalMyProp PostJ ) ->  (evalMyProp  (Post statePost) )).


Axiom wpModMon : forall stmtM  Post1 Post2 Pre1 Pre2 st,
(is_wpMod stmtM Post1 Pre1) ->  
(is_wpMod stmtM Post2 Pre2) -> 
 ( (evalMyProp (Post1 st) ) -> (evalMyProp (Post2 st)))    ->  
(forall st, ( (evalMyProp (Pre1 st) ) -> (evalMyProp (Pre2 st))) )   .

Axiom wpModFunInt : forall stmtM Post, exists Pre,  (is_wpMod stmtM Post Pre).



Lemma wpModImplieswp : forall stmtM  P Q  preM preJ listPogJ  stmtJ (assPost : myProp)  statePre  stateSP  zPre zPost,
                    ( is_wpMod  stmtM Q  preM ) ->
                    ( (evalMyProp ( P  statePre)) -> ( evalMyProp ( preM  statePre)) ) ->
                   (sp  ( (P statePre) , statePre, zPre, stmtM   ) (  stmtJ, assPost ,  stateSP,zPost  )) ->    
                   (wpAssume stmtJ Q   preJ listPogJ )  -> 
                                  ((evalMyProp ( preM statePre)  -> ( evalMyProp ( preJ statePre))) /\ 
                                         (forall s, (forall f: Assertion, (In f listPogJ) -> ( evalMyProp (f s)   )))).
Proof with  auto.


intro stmtM.
induction stmtM; intros until zPost; intros HwpMod Himply Hsp  HwpAssume. 


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

(* While *)
apply user.


(*Sequence*)
inversion HwpMod; subst...
inversion Hsp; subst ...
inversion HwpAssume; subst ...
eassert ( HrelWpSpS1 := (relWpSp _ _ _ _ _ _ _ _ _ _ H4 _ H2) )...

eassert(HindS2 := (IHstmtM2 (fun _ => ass1) Q pre_st2 p2 P2 st2j assPost state1 stateSP z1 zPost _ _ _ _))...
assert(Htotale := wpModFunInt stmtM1 p2).
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