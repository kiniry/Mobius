Require Import semantique. 
Require Import Ensembles.
Require Import List.
Require Import wp.
Require Import wpMod.
Require Import ZArith.
Require Import Classical.

(*a closed formula in the postcondition can be take out (and vice versa ) *)
Axiom  relClosFormWP : forall state ( P : myProp ) ( Post WP1 WP2  : Assertion ) stmtM,
   ( is_wpMod  stmtM Post  WP1 ) -> 
   ( is_wpMod  stmtM (fun s => ( p_and P  ( Post s )  ) )  WP2 ) -> 
   (  ( evalMyProp ( WP1 state) /\ (evalMyProp P )  ) -> 
   ( evalMyProp ( WP2 state) ) ) .  



(*sp ( stmt, pre) = post   ->  (post ->  pre) , PROVED BY JULIEN     *)
(*used in the case of a sequence*)
(* Axiom spStrongerThanPre : forall stmtm  stmtj Pre Post zPre zPost statePre statePost , 
 (sp (Pre , statePre , zPre , stmtm) ( stmtj , Post , statePost,  zPost )) -> ( (evalMyProp Post )->  (evalMyProp Pre ) ).
*)




 Inductive stmtJAssume : Set := 
 | SkipAssume : stmtJAssume
 |  AffectAssume : Var -> NumExpr -> stmtJAssume
(* | Assume  : State -> Assertion -> stmtJAssume*)
 | SeqAssume : stmtJAssume -> stmtJAssume -> stmtJAssume 
 | IfAssume : NumExpr -> stmtJAssume  ->  stmtJAssume  -> stmtJAssume  
(*note that the second argument is a list of pairs of prog variables and auxiliary variables, but we do not see the difference as both variables are from the type Var *)
 | WhileAssume : Invariant_j ->  list  ( Var * AuxVar ) -> NumExpr ->  stmtJAssume  ->  stmtJAssume  .

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
Inductive constructModVarSubstList : list Var -> Z ->  State -> list (Var * AuxVar) -> Set := 
 | empty : forall lVar   z state   lVarSubst , lVar = nil -> lVarSubst = nil ->  ( constructModVarSubstList lVar z state lVarSubst)
 | notEmpty : forall lVar   z ( lVarHead : Var)  lVarTail state lVarSubst lVarSubstHead lVarSubstTail,
          lVar = lVarHead :: lVarTail -> 
	  lVarSubst = lVarSubstHead :: lVarSubstTail ->
          lVarSubstHead = ( lVarHead ,  ( AuxName lVarHead z ) )   -> 
	  ( constructModVarSubstList lVarTail z  state lVarSubstTail) -> 
	  ( constructModVarSubstList lVar z  state lVarSubst ).

Definition nevalVar (s:State)(v: AllVar)  := 
match v with 
|  progvar varP => (neval s (nvar varP) )
|  auxvar varA => (neval s (nAuxVar varA) )
end.

(*creates a state which corresponds to the state at the loop borders and takes into account the modified variables *)
Definition stateAtLoop (state : State) ( z: Z) (lVar : list Var )  : State := 
                                                                         fun var: AllVar =>  
                                                                        match var with
                                                                        | progvar v' => 
                                                                            if  ( In_dec  varEqDec   v' lVar ) 
                                                                                 then (neval state (nAuxVar ( AuxName v' z ) ))
                                                                                 else  (neval state (nvar v')  )
                                                                         | auxvar v' => (neval state (nAuxVar v'))
                                                                         end.

Definition stateAtIf  (state : State ) (stateF : State) (stateT : State )(expB : NumExpr)  : State :=  
 fun v: AllVar => if ( Zeq  ( neval state  expB  )  0 )
         then (nevalVar stateF  v ) 
         else  ( nevalVar stateT v)
.

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
                            ( sp    ( ass, state, z , ( If Invariant_m expB  st1 st2) )  
                                             (  ( IfAssume expB  st1j   st2j  ),  p_or assF  assT , ( stateAtIf state stateF stateT expB)  , ze  ) )
  | isSpwhile : forall  expB stmt ass state inv lVar stmtj assIter stateIter z zIt lVarSubst,
                           ( isFresh z  ( fun st => ass) )    ->
                           ( isFresh z (fun st => (p_and (inv st) ( (p_eq (neval st expB)  0 ) ))) ) ->
                          (* the folowing condition is redundant wrt with the previous but suitable for the proof of the lemma p -> wp(st , sp(st, P)) *)
                          ( isFresh z (fun st => (inv st)) )->
                          ( isFresh z ( fun st => ( p_eq (neval st expB) 0 ) ) ) ->
                           let  stateWithMod := ( stateAtLoop  state z lVar )   in   
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
                                
(*RELATION WP AND SP *)
(* ( P -> WP(ST, Q) ) -> (Q -> SP (ST, P)) *)
Axiom relWpSp : forall stmtM stmtJ WP Pre Post SP zPre zPost statePre statePost ,
( is_wpMod  stmtM Post  WP ) ->
                    ( (evalMyProp ( Pre  statePre)) -> ( evalMyProp ( WP  statePre)) ) ->
 (sp  ( (Pre statePre) , statePre, zPre, stmtM   ) (  stmtJ, SP ,  statePost,zPost  )) ->    
((evalMyProp SP ) ->  (evalMyProp  (Post statePost) )).


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
                 let Cs := fun s => (p_implies (p_and  (inv s)  (p_neq (neval s cond) 0))  (pI s) )  in
                 let Ci := fun s => (p_implies (p_and (inv s) (p_eq (neval s cond)  0)) (post  s) ) in
                ( wpAssume (WhileAssume  (inv_j inv)  listModSubst cond stmt )  post inv  ( Cs :: Ci ::  PI ) ).

(* the axiom (which must be  a lemma ) says that  sp returns closed formulas *)
 (* Axiom spClosed :  forall stmtm stmtj Pre Post zPre zPost statePre statePost ,
(sp ( Pre , statePre , zPre , stmtm ) ( stmtj , Post , statePost, zPost ))  -> 
forall state , ( fun s : State => Post ) state = Post .  *)

(*CLOSED PREDICATES, DIFFERENT FROM FALSE, IN POST CAN BE TAKEN OUT WHEN APPLIED TO A WP FUNCTION *)
(* p CLOSED , ( P -> WP(ST, Q) ) -> ( P-> WP(ST,Q /\ P))*)
(* TODO THE PROOF *)
Axiom closedPredinPost :  
forall stmtM (P : myProp) ( Post  Wp1 Wp2 : Assertion )  , 
( is_wpMod  stmtM Post  Wp1  ) ->
( is_wpMod  stmtM ( fun st => p_and ( Post st ) P  )  Wp2 ) ->
forall state : State  , ( (evalMyProp P ) -> ( evalMyProp( Wp1 state ) ) ) ->
( (evalMyProp P ) -> (evalMyProp (Wp2 state ))) .
	   


Axiom evalClosedFormulas  : forall ( P : myProp ) (state : State ) ,  ( evalMyProp ( ( fun _ =>  P ) state )) = ( evalMyProp  P ).  

Axiom applicationToConstFuncts  : forall ( P : myProp ) (state : State ) ,  ( ( fun _ =>  P ) state )  =   P .  

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
(*commented because of the change in the sp def - add a check that z is fresh . clear stateWithMod; *) subst...
eassert(Hs := (IHstmtM _ _ _ _ _ _ _ H15 ))... (* originally the hypothesis was H11 . The proof Changed because  of the change in the sp def *)
simpl in Hpost.
simpl in Hs.
destruct Hpost as [[Hpost1 Hpost2] Hpost3]...

(* seq *)
inversion Hsp; subst...
eassert(Hs1 := (IHstmtM1 _ _ _ _ _ _ _ H1 )).
eassert(Hs2 := (IHstmtM2 _ _ _ _ _ _ _ H9 ))...
Qed.
 



(* wpMod  is monotone *)
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
              p_implies (p_not (p_in x lVar)) (p_eq (stf (progvar x) ) (st (progvar x)))))
          (invariant stf)) ) st ) )   ->  
 (evalMyProp ( ( fun stf : State =>
     p_foralls
       (fun st : State =>
        p_and
          (p_forallv
             (fun x : Var =>
              p_implies (p_not (p_in x lVar)) (p_eq (stf (progvar x)) (st (progvar x )))))
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

(**************************  wpMod represents a total function relation *********************************************************************)
Axiom wpModTotal: forall stmtM Post, exists Pre,  (is_wpMod stmtM Post Pre).
Axiom etaExpansion: forall s: State, s = (fun v : AllVar => s v).
(*need to be proven, may be not true *)
Axiom relationBtwStates: forall (P : Assertion ) ( fixedState :State )  (lVar : list Var ) (z : Z),
 ( isFresh z   P) ->
(evalMyProp ( p_exists (fun state =>  
                                           ( p_and      (p_forallv (fun x =>
                                                                   (p_implies (p_not (p_in x lVar)) (p_eq (state (progvar x) ) (fixedState (progvar x) )))))
                                                                   (P state) )))) ->
(evalMyProp (   P 
                    ( fun var : AllVar =>  match var with
                                                      | progvar v' => if (In_dec varEqDec v' lVar)
                                                                                 then (neval fixedState (nAuxVar ( AuxName v' z) ))  
                                                                                 else (neval fixedState  (nvar v') )
                                                      | auxvar v' =>   (neval fixedState (nAuxVar v')) 
                                                      end))).   

 Axiom spIsSurjective :  
forall  stmtM stmtJ ( statePre1 statePre2  statePost  : State ) ( Spost pre : myProp ) (z1 z2: Z) , 
(   sp (pre , statePre1, z1, stmtM)  (stmtJ , Spost , statePost, z2)  ) ->  
(   sp (pre, statePre2, z1, stmtM) (stmtJ , Spost , statePost, z2)  ) ->
 statePre1 = statePre2.

Axiom TRich : False.
Lemma Pre_implies_wp_of_sp : forall stmtM stmtJ PRE  sPost  zPre zPost statePre statePost wPre , 
  ( sp ( ( PRE  statePre ) , statePre , zPre, stmtM) ( stmtJ,  sPost , statePost, zPost ) )->  
  ( is_wpMod  stmtM ( fun s =>  sPost)  wPre ) -> 
  ( (evalMyProp ( PRE  statePre )) -> ( evalMyProp ( wPre  statePre ) ) ) .

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

elim TRich.

(*seq*)
inversion SP; subst...
inversion WP; subst ...

intros.
assert ( wpOfStmt1Ass1exists := wpModTotal stmtM1 (fun _ => ass1 )).
elim wpOfStmt1Ass1exists.
intros.
assert (HIndSt1 := IHstmtM1 st1j PRE ass1 zPre z1 statePre state1  x H1 H0 H).

assert (HIndSt2 := IHstmtM2 st2j  ( fun  state1 => ass1) sPost z1 zPost state1 statePost pre_st2 ).

rewrite (  applicationToConstFuncts ass1 state1) in HIndSt2.
assert (HIndSt22 := HIndSt2 H9 H2).
assert ( wpMonot := wpModMon stmtM1  ( fun st => ass1) pre_st2 x wPre H0 H5 ).
apply wpMonot.
intros.
apply (IHstmtM2 st2j  ( fun  st => ass1) sPost z1 zPost state1 statePost pre_st2 ).
assert ( spSurj := spIsSurjective stmtM2 st2j state1  st  statePost sPost ass1 z1 zPost   H9 ).
exact H9.


(*while *)

intros .
inversion SP ; subst ... 
inversion WP; subst ...
simpl in *.
split.

(*the invariant is proven *)
assert ( goal := H14 H). 
assumption.


(*the loop termination *)
simpl in *.
split.
assert ( goal := relationBtwStates ( fun st => p_and (inv st ) ( p_eq (neval st n)  0) )  statePre lVar z H11  ).
simpl in *.
intros.
destruct goal.
intros.
assert ( modVars_and_inv_notCond := ( conj ( conj H0 H1  ) H2) ).
exists st .
split.
destruct modVars_and_inv_notCond.
destruct H3.
assumption.
split.
assumption.
assumption.

simpl in *.
split.
split.
assert ( goal1 := relationBtwStates ( fun st => inv st )  statePre lVar z H12  ).
simpl in *.
intros.
apply goal1.
exists st;split; assumption.
assumption.

assert ( goal1 := relationBtwStates ( fun st =>  p_eq ( neval st n) 0 )  statePre lVar z H13  ).
simpl in *.
intros.
apply goal1.
exists st; split; assumption.
(*invariant preservation*)

(* from here not good *)

assert (existsWpPre := wpModTotal stmtM ( fun s => assIter ) ).
destruct existsWpPre.

assert (IndHyp :=
            IHstmtM 
            stmtj     
           (fun s => (p_and
           (newInv
              (fun var : AllVar =>
               match var with
               | progvar v' =>
                   if In_dec varEqDec v' lVar
                   then statePre (auxvar (AuxName v' z))
                   else statePre (progvar v')
               | auxvar v' => statePre (auxvar v')
               end))
           (p_not
              (p_eq
                 (neval
                    (fun var : AllVar =>
                     match var with
                     | progvar v' =>
                         if In_dec varEqDec v' lVar
                         then statePre (auxvar (AuxName v' z))
                         else statePre (progvar v')
                     | auxvar v' => statePre (auxvar v')
                     end) n) 0)) ) ) 
                     assIter 
                     (z + 1)
                     zPost
                    (*prestate*)
                    ( fun var : AllVar =>
                    match var with
                     | progvar v' =>
                     if In_dec varEqDec v' lVar
                        then statePre (auxvar (AuxName v' z))
                        else statePre (progvar v')
                     | auxvar v' => statePre (auxvar v')
                     end) 
                     (*poststate*)
                     stateIter
                     x 
                     H16 
                     H0 ).
simpl in *.
assert (spIterStrongerThanPre := spStrongerThanPre 
       stmtM 
       stmtj
       (*the precondition*)
       ( p_and
           (newInv
              (fun var : AllVar =>
               match var with
               | progvar v' =>
                   if In_dec varEqDec v' lVar
                   then statePre (auxvar (AuxName v' z))
                   else statePre (progvar v')
               | auxvar v' => statePre (auxvar v')
               end))
           (p_not
              (p_eq
                 (neval
                    (fun var : AllVar =>
                     match var with
                     | progvar v' =>
                         if In_dec varEqDec v' lVar
                         then statePre (auxvar (AuxName v' z))
                         else statePre (progvar v')
                     | auxvar v' => statePre (auxvar v')
                     end) n) 0)) ) 
                     (*the sp predicate*)
                     assIter
                     (z + 1)
                     
                     (zPost)
                     (*the prestate*)
                     (  fun var : AllVar =>
                           match var with
                           | progvar v' =>
                               if In_dec varEqDec v' lVar
                               then statePre (auxvar (AuxName v' z))
                               else statePre (progvar v')
                           | auxvar v' => statePre (auxvar v')
                           end )
                     stateIter
                     H16
 ).
simpl in *.


  assert ( assIter_implies_inv : 
              (evalMyProp assIter) ->  (evalMyProp ( (  fun stf : State =>
              p_foralls
                  (fun st : State =>
                        p_and
                        (p_forallv
                           (fun x : Var =>
                                   p_implies (p_not (p_in x lVar))
                                   (p_eq (stf (progvar x)) (st (progvar x))))) (inv stf)) ) 
                          (fun var : AllVar =>
                                match var with
                                | progvar v' =>
                                    if In_dec varEqDec v' lVar
                                    then statePre (auxvar (AuxName v' z))
                                    else statePre (progvar v')
                                | auxvar v' => statePre (auxvar v')
                                end)   ))).
intros.
simpl in *.
assert ( invInPost := spIterStrongerThanPre H1).
split.
destruct invInPost as [ [[Pre InvAtIter] NotMod ]  NotCond]     .
intros.
assert ( notMod := H4 var H6).









(************************************************************************************************)
 Lemma wpModImplieswp : forall stmtM  P Q preM preJ listPogJ  stmtJ (assPost : myProp)  statePre  stateSP  zPre zPost,
                    ( is_wpMod  stmtM Q  preM ) ->
                    ( (evalMyProp ( P  statePre)) -> ( evalMyProp ( preM  statePre)) ) ->
                   (sp  ( (P statePre) , statePre, zPre, stmtM   ) (  stmtJ, assPost ,  stateSP,zPost  ) ) ->  
                   (wpAssume stmtJ Q  preJ listPogJ )  -> 
                                  ((evalMyProp ( P statePre)  -> ( evalMyProp ( preJ statePre)) )  /\ 
                                         (forall s, (forall f: Assertion, (In f listPogJ) -> ( evalMyProp (f s)   )))).

Proof with  auto.


intro stmtM.
induction stmtM; intros until zPost; intros HwpMod Himply Hsp  HwpAssume. 

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


subst ...
simpl ...
intros .
assert ( pre_inv_cond_impl_p :  ( 
                            forall st : State,
                             (   evalMyProp (P statePre) )  /\
                            (forall var : Var,
                            ~ In var lVar -> st (progvar var) = statePre (progvar var)) ->
                            evalMyProp (inv st) -> neval st n <> 0 -> evalMyProp (pre_st st) /\    (   evalMyProp (P statePre )))   ).

split.
destruct H as [ [ [ P_in_statePre invInState  ]   varNotMod ] condInState].
assert ( impliesWP :=  Himply  P_in_statePre ).
destruct impliesWP.
destruct H3.
destruct H0.
assert ( pre_stHolds := H4 st  H5 H1 H2 ).
assumption.
destruct H0.
assumption.
simpl in *.
assert (wpExistsForInvAndP :=wpModTotal  
   stmtM  
   (fun st => p_and 
              (P statePre)
             ( ( fun stf : State =>
                 p_foralls
                    (fun st : State =>
                         p_and
                             (p_forallv
                                 (fun x : Var =>
                                 p_implies (p_not (p_in x lVar))
                                 (p_eq (stf (progvar x)) (st (progvar x))))) (inv stf) ) ) st )
                                )
).

destruct wpExistsForInvAndP.
simpl in *.
assert ( hyp_wp_and_P_impl_wpOfP := relClosFormWP   
   statePre 
   ( P statePre )
   ( fun stf : State =>
                 p_foralls
                    (fun st : State =>
                         p_and
                             (p_forallv
                                 (fun x : Var =>
                                 p_implies (p_not (p_in x lVar))
                                 (p_eq (stf (progvar x)) (st (progvar x))))) (inv stf)))
      pre_st
      x
      stmtM 
      H6
      H0).

simpl in *.
(*  ************* *)
assert ( pre_inv_cond_impl_p1 := pre_inv_cond_impl_p statePre ).
assert( trans : (evalMyProp (P statePre) /\
                       (forall var : Var,
                        ~ In var lVar ->
                        statePre (progvar var) = statePre (progvar var))  /\ 
                       evalMyProp (inv statePre) /\ 
                       neval statePre n <> 0) -> evalMyProp (x statePre) ).
intros.
destruct H1  .
destruct H2.
destruct H3.
assert ( pre_stAndP :=pre_inv_cond_impl_p1 (conj  H1 H2 ) H3 H4). 
assert (wpForInvAndP :=  hyp_wp_and_P_impl_wpOfP pre_stAndP ).
assumption.
assert (ind  := IHstmtM      
        (fun s => (p_and
        ( p_and 
        ( p_and  (P statePre) 
        ( p_forallv (fun var =>
         p_implies (p_not (p_in var lVar)) (  p_eq ( statePre (progvar var) ) (  statePre (progvar var) )))))
          (inv statePre)  )
         (p_neq (neval statePre n ) 0 ) ) )

     (fun st : State =>
     p_and (P statePre)
       (p_foralls
          (fun st0 : State =>
           p_and
             (p_forallv
                (fun x : Var =>
                 p_implies (p_not (p_in x lVar))
                   (p_eq (st (progvar x)) (st0 (progvar x))))) (inv st))))
                   x  
                   pI 
                   PI 
                   stmtj 
                   assIter  
                   statePre 
                   stateIter 
                   (z+1) 
                   zPost 
                   H0  
).
rewrite (evalClosedFormulas  ( p_and
             (p_and
                (p_and (P statePre)
                   (p_forallv
                      (fun var : Var =>
                       p_implies (p_not (p_in var lVar))
                         (p_eq (statePre (progvar var))
                            (statePre (progvar var)))))) (inv statePre))
             (p_neq (neval statePre n) 0))  statePre ) in ind.
simpl in *.


assert (trans1 : (((evalMyProp (P statePre) /\
         (forall var : Var,
          ~ In var lVar -> statePre (progvar var) = statePre (progvar var))) /\
        evalMyProp (inv statePre)) /\ neval statePre n <> 0 ->
       evalMyProp (x statePre)) ).
intros.
destruct H1 as [ [ [H2 H3] H4 ] H5].
assert ( trans2 :=  trans (conj H2 (conj H3  (conj H4  H5 ) ) ) ) . 
assumption.
assert ( ind1 := ind trans1 H15 ).

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