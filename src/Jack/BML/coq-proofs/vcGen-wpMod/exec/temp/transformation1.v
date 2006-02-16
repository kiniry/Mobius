Require Import semantiqueAux1. 
Require Import Ensembles.
Require Import List.
(* Require Import wp. *)
Require Import wpModAux1.
Require Import wpAssume1.
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




 

(*old version *)
(*constructing a  new auxiliary variable corresponding to the value of the variable given as first parameter at program state given as second parameter *)
(* Inductive constructModVarSubstList : list Var -> Z ->  State -> list (Var * AuxVar) -> Set := 
 | empty : forall lVar   z state   lVarSubst , lVar = nil -> lVarSubst = nil ->  ( constructModVarSubstList lVar z state lVarSubst)
 | notEmpty : forall lVar   z ( lVarHead : Var)  lVarTail state lVarSubst lVarSubstHead lVarSubstTail,
          lVar = lVarHead :: lVarTail -> 
	  lVarSubst = lVarSubstHead :: lVarSubstTail ->
          lVarSubstHead = ( lVarHead ,  ( AuxName lVarHead z ) )   -> 
	  ( constructModVarSubstList lVarTail z  state lVarSubstTail) -> 
	  ( constructModVarSubstList lVar z  state lVarSubst ). *) 



(*creates a state which corresponds to the state at the loop borders and takes into account the modified variables *)
(* Definition stateAtLoop (state : State) ( z: Z) (lVar : list Var )  : State := 
                                                                         fun var: AllVar =>  
                                                                        match var with
                                                                        | progvar v' => 
                                                                            if  ( In_dec  varEqDec   v' lVar ) 
                                                                                 then (neval state (nAuxVar ( AuxName v' z ) ))
                                                                                 else  (neval state (nvar v')  )
                                                                         | auxvar v' => (neval state (nAuxVar v'))
                                                                         end. *)

Definition stateAtIf  ( auxState : AuxState )  (state : State ) (stateF : State) (stateT : State )(expB : NumExpr)  : State :=  
 fun v: Var => if ( Z_eq_dec  ( neval state   auxState expB  )  0 )
         then ( stateF v  ) 
         else  ( stateT v) .

Inductive sp :  myProp * State *AuxState * stmt_m -> stmtJAssume * myProp  * State *AuxState -> Prop := 
   | isSpSkip : forall state stateAux z ass , 
                            sp  (ass,state, stateAux,  SkipInd  Invariant_m z)  (SkipAssume z,   ass,  state, stateAux )
   | isSpAssign : forall var expr  ass state stateAux z , 
                            sp (ass, state, stateAux, AffectInd  Invariant_m z var expr) 
                                (AffectAssume z var expr, ass, update state var (neval  state stateAux expr), stateAux)
   | isSpSeq : forall  st1 st2 ass state ass1 state1 ass2 state2  stateAux st1j st2j z  , 
                            ( sp    (ass  , state ,stateAux  ,  st1  )       (st1j, ass1,  state1 , stateAux) ) ->
                            ( sp    (ass1, state1, stateAux, st2  ) (  st2j, ass2, state2, stateAux ) ) -> 
                            ( sp    (ass, state,  stateAux, (SeqInd  Invariant_m z st1 st2) ) 
                                      ( ( SeqAssume z st1j st2j ), ass2, state2, stateAux  ))
   | isSpIf : forall   expB st1 st2 ass state assT assF  stateT stateF stateAux  st2j st1j z , 
                            (forall v : Var , (stateAux (AuxName v z) ) = (state v) )->
                            (sp  (  ( p_and  ( p_neq  ( neval (FreezeVarAtState state stateAux z) stateAux   expB  )  0 ) ass   ), (FreezeVarAtState state stateAux z) ,  stateAux, st1 )  
                                       (  st1j, assT, stateT, stateAux  ) ) ->
                            (sp  ( 
                                     ( p_and   ( p_eq ( neval (FreezeVarAtState state stateAux z)   stateAux  expB  )  0 )   ass  ), (FreezeVarAtState state stateAux z),  stateAux, st2 )   
                                     (  st2j, assF, stateF, stateAux ) 
                                   ) ->    
                            (sp  
                                  ( ass, 
                                     state,  
                                     stateAux,
                                     ( IfInd Invariant_m z expB  st1 st2) )  
                                   ( ( IfAssume z ( (FreezeVarAtState state stateAux z), stateAux)   expB  st1j   st2j  ),  
                                     p_or assF  assT , 
                                     ( stateAtIf stateAux state stateF stateT expB) ,
                                     stateAux
                                   ) 
                            )
  | isSpwhile : forall  expB stmt ass state inv lVar stmtj assIter stateIter auxStateIterStart  auxStateLoopEnd  auxStateEndIter auxState  z  ,
                           ( isFresh z  ass )    ->
                           ( isFresh z ( p_and (inv (state, auxState) ) ( (p_eq (neval state auxState  expB)  0 ))) ) ->
                           (* the following condition is redundant wrt with the previous but suitable for the proof of the lemma p -> wp(st , sp(st, P)) *)
                           ( isFresh z  (inv (state, auxState ) ) )->
                           ( isFresh z  ( p_eq (neval state auxState  expB) 0 ) )->
                           (*the three states : state - before the loop, 
                                                            stateIterStart - at the beginning of every iteration 
                                                            stateLoopEnd - at the end of the loop *)
                           (forall v : Var , (~ In v lVar) ->  (  getVarValAtState  z v ) = (state v) )->
                           let newInv :=  (fun st : State*AuxState =>
                                                           let (s, sAux) :=  st in
                                                           ( p_and (p_and ass  ( inv (s , sAux) ) )  
                                                                        ( p_forallv ( fun v: Var => (p_implies (p_not ( p_in  v lVar))    
                                                                                                            ( p_eq ( getVarValAtState z v  ) 
                                                                                                            ( neval s sAux (nvar v) ))))))) in
                                                                                            
                           (evalMyProp ass -> evalMyProp (inv (state, auxState))) -> 
                            (* the interpretation of the auxiliary vars auxStateLoopEnd is such that  the propagated predicate for the loop body holds *)
                           (evalMyProp ( p_and 
                                                 (p_eq ( neval  ( stateAtLoop  state auxStateLoopEnd  z lVar )  auxStateLoopEnd   expB )  0 ) 
                                                 ( inv   ( ( stateAtLoop  state auxStateLoopEnd z lVar ),  auxStateLoopEnd) ) 
                                                ) )  ->
			(*the interpretation of the auxiliary vars auxStateIterStart is such that the strongest postcondition predicate also holds*)
		          ( evalMyProp  
			      (p_and (p_and ass ( inv ( ( stateAtLoop  state auxStateIterStart z lVar ) , auxStateIterStart ) ))   
                                                ( p_not( p_eq ( neval   ( stateAtLoop  state auxStateIterStart z lVar )  auxStateIterStart expB )  0) )) 
			   ) ->
                           (*CONSTRUCT THE SUBSTITUTION lIST*)
			  (* ( constructModVarSubstList lVar z ( stateAtLoop  state stateAux z lVar )  lVarSubst ) ->  *)
                          (sp  ( (p_and (  p_and ass ( inv ( ( stateAtLoop  state auxStateIterStart z lVar ) , auxStateIterStart ) ))   
                                                   ( p_not( p_eq ( neval   ( stateAtLoop  state auxStateIterStart z lVar )  auxStateIterStart expB )  0) )) ,
                                    ( stateAtLoop  state auxStateIterStart  z lVar )  , 
                                    auxStateIterStart,
                                    stmt
                                  ) 
                                 (
                                   stmtj, 
                                   assIter, 
                                   stateIter ,
                                   auxStateEndIter
                                 ) )  -> 
                           ( sp    ( ass,  
                                       state, 
                                       auxState,
                                       WhileInd  Invariant_m z expB ( inv_m  inv lVar )  stmt 
                                     )                                                   
                                     ( WhileAssume z (inv_j newInv) ( ( stateAtLoop  state auxStateLoopEnd z lVar ), auxStateLoopEnd )  expB stmtj   ,                                    
                                            p_and  ( 
                                               p_and (  inv ( ( stateAtLoop  state auxStateLoopEnd z lVar ) , auxStateLoopEnd ) ) ass )
                                                          (  p_eq  ( neval ( stateAtLoop state auxStateLoopEnd  z lVar )  auxStateLoopEnd expB )  0 ), 
                                             ( stateAtLoop  state auxStateLoopEnd  z lVar )  ,
                                             auxStateLoopEnd
                                      )
                           ).
                                

Axiom evalClosedFormulas  :  forall ( P : myProp ) (state : State ) ,  ( evalMyProp ( ( fun _ =>  P ) state )) = ( evalMyProp  P ).  

Axiom applicationToConstFuncts  : forall ( P : myProp ) (state : State ) ,  ( ( fun _ =>  P ) state )  =   P .  
(*
(*need to be proven, may be not true *)
 Axiom relationBtwStates: forall (P : Assertion ) ( fixedState :State ) (auxState : AuxState )
 (lVar : list Var ) (z : Z),
 ( isFresh z   P) ->
(evalMyProp ( p_exists (fun state =>  
                                           ( p_and      (p_forallv (fun x =>
                                                             (p_implies
                                                                     (p_not (p_in x lVar))
                                                                     (p_eq (state  x ) (fixedState  x )))))
                                                            
                                                                    (P  (state,  auxState))))))->
(exists auxState , evalMyProp (   P  
                   ( ( fun var : Var =>   if (In_dec varEqDec var lVar)
                                                         then (auxState ( AuxName var z) )  
                                                         else (neval fixedState  auxState (nvar var) )
                     ) , auxState ))).    
*)
 Lemma spCorrectness : 
forall stmtM stmtJ state1 state2 stateAux1 stateAux2 (Pre : Assertion  ) ( SP : myProp ) , 
  (sp  ( (Pre  (state1, stateAux1) ) , state1, stateAux1, stmtM   ) ( stmtJ , SP ,  state2, stateAux2  ) )  ->
( evalMyProp  (Pre (state1, stateAux1 ) ) -> ( evalMyProp SP)) .  
Proof with auto.
intros stmtM; induction stmtM; intros until SP ; intros HStrongestPost HPreHolds .

(*skip*)
inversion HStrongestPost; subst ...


(*assign*)
inversion HStrongestPost; subst ...

(*if *)
inversion HStrongestPost; subst ...
assert ( HInd1 := IHstmtM1 
                              st1j 
                              (FreezeVarAtState state1 stateAux2 z) 
                              stateT
                              stateAux2
                              stateAux2
                              (fun _ => p_and (p_neq (neval (FreezeVarAtState state1 stateAux2 z)  stateAux2 n) 0) (Pre (state1,  stateAux2)))
                              assT ).

 rewrite
 ( applicationToConstFuncts ( p_and (p_neq (neval state1 stateAux2 n) 0) (Pre (state1, stateAux2)) ) state1 ) in 
 HInd1.
(* rewrite <- (progExprEvalProp1 stateAux) in H1. *)

assert ( HInd1Simpl :=  HInd1 H11 ).
simpl in *.
clear HInd1.
assert ( HInd2 := IHstmtM2
                              st2j 
                              (FreezeVarAtState state1 stateAux2 z) 
                              stateF
                              stateAux2
                              stateAux2
                              (fun _ => 
                                 p_and (p_eq (neval (FreezeVarAtState state1 stateAux2 z)  stateAux2 n) 0) (Pre (state1, stateAux2) ) ) 
                              assF
                              ).

 rewrite
 ( applicationToConstFuncts ( p_and (p_eq (neval state1 stateAux2 n) 0) (Pre (state1, stateAux2)) ) state1 ) in  HInd2.
(* rewrite <- (progExprEvalProp1 stateAux) in H10. *)
assert ( HInd2Simpl :=  HInd2 H12 ).
simpl in *.
clear HInd2.
assert (thiersExclu := classic  ((neval (FreezeVarAtState state1 stateAux2 z)   stateAux2 n) = 0 ) ).
destruct thiersExclu.
assert ( assertAssF  := HInd2Simpl  (conj H HPreHolds  )  ).
left.
assumption.
assert ( assertAssF  := HInd1Simpl  (conj H HPreHolds  )  ).
right.
assumption.


(*while *)

inversion HStrongestPost. 
unfold newInv in *.

subst ...
simpl in *.
intros.
destruct H16.
split .
split.
assumption.
assumption.
assumption.

(* sequence *)
inversion HStrongestPost; subst ...
assert ( HIndSt1 := IHstmtM1   st1j state1 state0  stateAux2  stateAux2 Pre ass1  H1 ).
assert ( HIndSt2 := IHstmtM2   st2j state0 state2 stateAux2 stateAux2  (fun _ => ass1) SP   H10 ).
 rewrite ( applicationToConstFuncts ass1 state0  ) in  HIndSt2.
apply HIndSt2.
apply HIndSt1.
assumption.
Qed.








 
(* the axiom (which must be  a lemma ) says that  sp returns closed formulas *)
 (* Axiom spClosed :  forall stmtm stmtj Pre Post zPre zPost statePre statePost ,
(sp ( Pre , statePre , zPre , stmtm ) ( stmtj , Post , statePost, zPost ))  -> 
forall state , ( fun s : State => Post ) state = Post .  *)

(*CLOSED PREDICATES, DIFFERENT FROM FALSE, IN POST CAN BE TAKEN OUT WHEN APPLIED TO A WP FUNCTION *)
(* p CLOSED , ( P -> WP(ST, Q) ) -> ( P-> WP(ST,Q /\ P))*)
(* TODO THE PROOF *) 
(*the old formulation of the axiom, simpler but the new one is easier to apply *)
(* Axiom closedPredinPost :  
forall stmtM (P : myProp) ( Post  Wp1  Wp2 : Assertion )  , 
( is_wpMod  stmtM Post  Wp1  ) ->
( is_wpMod  stmtM ( fun st => p_and ( Post st ) P  )  Wp2 ) ->
forall state : State  , ( (evalMyProp P ) -> ( evalMyProp( Wp1 state ) ) ) ->
( (evalMyProp P ) -> (evalMyProp (Wp2 state ))) . *) 
	   

(* p CLOSED , ( P -> WP(ST, Q) ) -> ( P-> WP(ST,Q /\ P))*)
(* a  new formulation *)
Axiom closedPredinPost :  
forall stmtM (P Q : myProp) ( Post  Wp1  Wp2 : Assertion )  , 
( is_wpMod  stmtM Post  Wp1  ) ->
( is_wpMod  
       stmtM 
       ( fun s : State * AuxState => 
                   let (st, stAux) := s in p_and ( Post (st, stAux))   P    )  
       Wp2 ) ->
forall (state : State)  (stateAux : AuxState)  , 
        ( ((evalMyProp P ) /\ (evalMyProp Q ) )  -> ( evalMyProp( Wp1 (state, stateAux) ) ) ) ->
        ( ((evalMyProp P ) /\ (evalMyProp Q ) )  -> (evalMyProp (Wp2 (state , stateAux) ))) .

Lemma spStrongerThanPre : forall stmtm  stmtj Pre Post statePre statePost stateAuxPre stateAuxPost, 
  (sp (Pre , statePre , stateAuxPre , stmtm) ( stmtj , Post , statePost, stateAuxPost  )) -> 
  ( (evalMyProp Post )->  
  (evalMyProp Pre ) ).
 Proof with auto.
 intros stmtM; induction stmtM; intros until stateAuxPost; intros Hsp Hpost.
inversion Hsp; subst...
inversion Hsp; subst...
inversion Hsp; subst...
simpl in Hpost.

 destruct Hpost.

assert(Hfalse := (IHstmtM2  _ _ _ (FreezeVarAtState statePre stateAuxPost z)   _  _ stateAuxPost H12 H)).
simpl in Hfalse; destruct Hfalse...
assert(Htrue := (IHstmtM1 _ _ _ _ _ _  stateAuxPost H11 H)).
simpl in Htrue; destruct Htrue...

(* while *)
inversion Hsp. 
(* unfold stateWithMod in H1, H7, H8, H10, H11, H; *)
(*commented because of the change in the sp def - add a check that z is fresh . clear stateWithMod; *) 
unfold newInv in *.
subst...
simpl in *.
intuition.

(* assert(Hs := (IHstmtM _ _ assIter  _ _ _ H17  ))... 
(* originally the hypothesis was H11 . The proof Changed because  of the change in the sp def *)
simpl in Hpost.
simpl in Hs.
destruct Hpost as [[Hpost1 Hpost2] Hpost3]...
*)

(* seq *)
inversion Hsp; subst...
assert(Hs1 := (IHstmtM1 _ _ _ _ _ _ stateAuxPost H1 )).
assert(Hs2 := (IHstmtM2 _ _ _ _ _ _ stateAuxPost H10 ))...
Qed.
 




(**************************  wpMod represents a total function relation *********************************************************************)
Axiom wpModTotal : forall stmtM Post, exists Pre,  (is_wpMod stmtM Post Pre).
Axiom etaExpansion: forall s: State, s = (fun v : Var => s v).
(*RELATION WP AND SP *)
(* ( P -> WP(ST, Q) ) -> (Q -> SP (ST, P)) *)
Lemma  relWpSp : forall stmtM stmtJ WP Pre Post SP  statePre statePost stateAuxPre stateAuxPost ,
( is_wpMod  stmtM Post  WP ) ->
                    ( (evalMyProp ( Pre  (statePre, stateAuxPre ))) -> 
                                ( evalMyProp ( WP  (statePre, stateAuxPre ))) ) ->
 (sp  ( (Pre (statePre, stateAuxPre)) , statePre , stateAuxPre, stmtM   ) (  stmtJ, SP ,  statePost, stateAuxPost  )) ->    
((evalMyProp SP ) ->  (evalMyProp  (Post (statePost, stateAuxPost ) ) )).


Proof with auto.
intro stmtM; induction stmtM; intros until stateAuxPost; intro hypWP; intro hypWP_Implied; intro hypSP.
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

(*get some hyps for the then case*)
assert ( HypWpThen : (  neval statePre stateAuxPost n <> 0 /\ evalMyProp (Pre ( statePre, stateAuxPost ))  )-> evalMyProp (pre_t (statePre, stateAuxPost)) ).
intros.
destruct H.
assert ( hypWpImp := hypWP_Implied H0 ).
destruct hypWpImp...

assert (hypIndThen := ( IHstmtM1 st1j   pre_t   ( fun s => let (st, stAux ) := s in (  p_and (p_neq (neval st stAux n)  0 )  ( Pre (st, stAux) )  )) Post assT  statePre stateT  _ stateAuxPost H6 HypWpThen  ) )...
rewrite (semAux3 statePre stateAuxPost n z H2 ) in H13.
rewrite (extensionality _ _  ( FreezeVarAtState statePre stateAuxPost z ) statePre  ) in H13.
Focus 2.
apply ( semAux5 statePre stateAuxPost z H2).
simpl in *.
assert ( hypIndThen1 := hypIndThen H13  ).


(*get some hyps for the  else case*)
assert ( HypWpElse : (  neval statePre stateAuxPost n = 0 /\ evalMyProp (Pre ( statePre, stateAuxPost ))  )-> evalMyProp (pre_f (statePre, stateAuxPost)) ).
intros.
destruct H.
assert ( hypWpImp := hypWP_Implied H0 ).
destruct hypWpImp...
(*HypWpElse proven *)
assert (hypIndElse := ( IHstmtM2 st2j   pre_f  ( fun s =>let (st, stAux ) := s in (  p_and (p_eq (neval st stAux n)  0 )  ( Pre (st, stAux))  ))  Post assF  statePre stateF  stateAuxPost stateAuxPost H5 HypWpElse ) )...
rewrite (semAux3 statePre stateAuxPost n z H2 ) in H14.
rewrite (extensionality _ _  ( FreezeVarAtState statePre stateAuxPost z ) statePre  ) in H14.
Focus 2.
apply ( semAux5 statePre stateAuxPost z H2).
simpl in *.
assert ( hypIndElse1 := hypIndElse H14  ).
assert(hStrT := (spStrongerThanPre _ _ _ _ _ _ _ _  H13)).
assert(hStrF := (spStrongerThanPre _ _ _ _ _ _ _ _  H14)).
 simpl in hStrT, hStrF.
unfold stateAtIf.
case (Z_eq_dec (neval statePre stateAuxPost n) 0 ) .

intro cond.
simpl.
rewrite <- (etaExpansion stateF).
destruct SPholds as [ assFProof | assTProof ].
apply hypIndElse1.
assumption.
assert  (Haha := hStrT assTProof ).
destruct Haha.
contradiction.


intro notcond.
simpl.
rewrite <- (etaExpansion stateT).
destruct SPholds as [ assFProof | assTProof ].

assert  (Haha := hStrF assFProof ).
destruct Haha.
contradiction.
apply hypIndThen1.
assumption.

(* while *)
inversion hypSP; subst...
simpl.
inversion hypWP; subst...
intros h.
destruct h as [[h1 h2] h3].
simpl in hypWP_Implied.
assert(h4 := hypWP_Implied h2).
destruct h4 as [ h4 [h5 [ h6 h7]] ].
apply h7.
intros.
unfold stateAtLoop. 
case (In_dec varEqDec var lVar).
intros.
contradiction.
intros.
apply h5.
assumption.
assumption.
assumption.


(* Seq *)
inversion hypSP; subst...
inversion hypWP; subst...
intros.
assert(Hind1 := IHstmtM1 st1j  _  _  _ _ _ _ _ _    H6 hypWP_Implied   H1 ) .
assert(Hind2 := IHstmtM2 st2j  _ (fun _ => ass1) _ _ _ _ _ _   H5 Hind1 H10)...

Qed.



(*a condition that the loop invariants are correct must be added  *)
(* Lemma Pre_implies_wp_of_sp : forall stmtM stmtJ ( PRE : myProp ) 
sPost statePre statePost auxStatePre auxStatePost  wPre , 
  ( sp ( PRE   , statePre , auxStatePre, stmtM) ( stmtJ,  sPost , statePost,  auxStatePost  ) )->  
  ( is_wpMod  stmtM ( fun s =>  sPost)  wPre ) -> 
  (   (evalMyProp  PRE  ) -> ( evalMyProp ( wPre  (statePre , auxStatePre ) ) )  ) .

Proof with auto.
intro stmtM. induction stmtM; intros until wPre; intro SP;  intro WP.

(*skip *) 
 inversion SP. (*  ; subst ... *)  
 inversion WP. (* ; subst ... *) 
intros.
assumption.


(*assign*)
inversion SP; subst ... 
inversion WP  ; subst ...
intros.
intuition.


(*if*)

inversion SP ; subst ... 
inversion WP; subst ...

simpl in *.
split.

(*then case *)
assert ( existsWpThen := wpModTotal  stmtM1 (fun s  => assT)  ).
elim existsWpThen. 
intro wpExists. 
intro wpAssT.

assert ( IHypThen1 :=  (IHstmtM1 st1j (   p_and (p_neq (neval (FreezeVarAtState statePre auxStatePost z) auxStatePost n) 0) PRE )   assT   (FreezeVarAtState statePre auxStatePost z) stateT auxStatePost _ wpExists  H12 wpAssT)).
 (* exact H1. *)

assert ( Then_impl_ThenOrElse :  forall state stAux,
                       ( evalMyProp ( (fun _  => assT)  ( state, stAux) ) ) ->
             (  evalMyProp ( (fun s : State * AuxState  => p_or assF assT) (state, stAux) ) )    ).
intros.
simpl in *.
right. 
assumption.
assert ( applyMonotThenInStatePre := ( wpModMon 
                                        stmtM1  
                                        ( fun s => assT) 
                                        (fun s => (  p_or assF assT)  ) 
                                        wpExists 
                                        pre_t  
                                        wpAssT 
                                        H8    
                                        Then_impl_ThenOrElse  
                                        ) ).
simpl in *.
intro cond.
rewrite <- ( semAux3 statePre auxStatePost n z) in cond.
assert ( wpExistsHoldsInState0 :=  IHypThen1   (conj cond H)  ).
(* assumption. *)
simpl in *.
apply (applyMonotThenInStatePre statePre  auxStatePost ).
unfold State, AuxState.
rewrite <- (semAux4 statePre auxStatePost wpExists z H3).
assumption.
assumption.

(*else case *)
assert ( existsWpElse := wpModTotal  stmtM2 (fun s  => assF)  ).
elim existsWpElse. 
intro wpExists. 
intro wpAssF.
assert ( IHypElse1 :=  (IHstmtM2   
                                        st2j 
                                        (  p_and (p_eq (neval  (FreezeVarAtState statePre auxStatePost z)  auxStatePost n) 0)   PRE  )  
                                        assF    
                                        (FreezeVarAtState statePre auxStatePost z)  
                                        stateF 
                                        auxStatePost  
                                        _
                                        wpExists 
                                        H13
                                        wpAssF  )).
(* exact H11. *) 
assert ( Else_impl_ThenOrElse :  forall state stAux,
                       ( evalMyProp ( (fun _  => assF)  ( state, stAux) ) ) ->
             (  evalMyProp ( (fun s : State * AuxState  => p_or assF assT) (state, stAux) ) )    ).
intros.
simpl in *.
left. 
assumption.
assert ( applyMonotElseInStatePre := ( wpModMon 
                                        stmtM2 
                                        ( fun s => assF) 
                                        (fun s => (  p_or assF assT)  ) 
                                        wpExists 
                                        pre_f  
                                        wpAssF 
                                        H7   
                                        Else_impl_ThenOrElse  
                                        ) ).
simpl in *.
intro notCond.
rewrite <- ( semAux3 statePre auxStatePost n z) in notCond.
assert ( wpExistsHoldsInState0 :=  IHypElse1   (conj notCond H)  ).
(* assumption. *)
simpl in *.
apply (applyMonotElseInStatePre statePre  auxStatePost ).
unfold State, AuxState.
rewrite <- (semAux4 statePre auxStatePost  wpExists z H3).
assumption.
assumption.




(*while *)
inversion WP; subst ...
inversion SP; subst ... 


simpl in *.
split.
apply H18.
assumption.
intuition.
assert ( relBtwPost := spStrongerThanPre 
                                       stmtM 
                                       stmtj 
                                       ( p_and
                                              (p_and PRE
                                                    (invariant (stateAtLoop statePre auxStateIterStart z lVar, auxStateIterStart )))
                                       (p_not (p_eq (neval (stateAtLoop statePre  auxStateIterStart z lVar) auxStateIterStart n) 0)))  
                                       assIter 
                                       ( stateAtLoop statePre auxStateIterStart z lVar) 
                                       stateIter 
                                       auxStateIterStart
                                       auxStateEndIter
                                       H21
                                       ).



assert (   existsWp := wpModTotal stmtM  ( fun s =>assIter )). 
destruct existsWp.
assert ( HI1 :=   IHstmtM 
                           stmtj 
                           ( p_and
                                   (p_and PRE
                                         (invariant (stateAtLoop statePre auxStateIterStart z lVar, auxStateIterStart)))
                                   (p_not
                                         (p_eq (neval (stateAtLoop statePre auxStateIterStart z lVar) auxStateIterStart n) 0)))
                           assIter 
                           ( stateAtLoop statePre auxStateIterStart z lVar) 
                           stateIter 
                           auxStateIterStart
                           auxStateEndIter
                           x
                          H21    
                          H12
                   ).
simpl in *.
simpl in *.
intros.
assert ( assIter_implies_invAtStateLoop:  
forall (state : State) ( stateAux: AuxState) , 
evalMyProp assIter ->
 evalMyProp (invariant (stateAtLoop statePre auxStateIterStart z lVar, auxStateIterStart ))) .
intuition.
assert ( wpMonot :=  wpModMon _ _ _ _ _ H12 H6).
simpl in *.
apply wpMonot.
intuition.

destruct inv_in_conj .
destruct H1.
assumption.
monot
(*seq*)
Qed. 

	   
*)





(**************************  wpMod represents a total function relation *********************************************************************)


Theorem closedPredOutOfQuant : 
forall (P: Prop) (Q:State -> Prop), 
(P /\ forall st : State , Q st )->(forall st : State , (P /\  Q st) ).
Proof.
intros.
intuition.
Qed.
 Axiom Reduct1 : forall (P : Assertion) ( state :State) (stateAux : AuxState) ,
(evalMyProp  (P  (state, stateAux) ) ) = ( evalMyProp 
                                       ( (   fun (st : State*AuxState) => 
                                           let  (s, sAux) := st in
                                           (P (s, sAux)) 
                                       ) 
                                       (state, stateAux)) ).
(************************************************************************************************)
 (*relation between formulas and substituted formulas *)
Lemma  pogSubstRelation  : forall st auxSt ( l lSubst : list Assertion ) , 
              (pogSubst l st auxSt lSubst) ->
              (forall f state , ( In f l )  -> evalMyProp (f (state, auxSt ))    ) -> 
              ( forall f state , ( In f lSubst )  -> evalMyProp( f (state, auxSt ))   ). 

Proof.
intros state auxState lis lisSubst pogSubstRel f_In_list_hold.
induction pogSubstRel .
intros.
apply f_In_list_hold.
assumption.

intros.
destruct H.
assert ( hypHeadInList : In head (head :: tail)  ).
apply (in_eq head tail ).
assert ( HHH := f_In_list_hold head state hypHeadInList ).
subst.
rewrite <- H.
assumption.
assert  (  forall (f : Assertion) (state : State),
                 In f tail -> evalMyProp (f (state, auxState))    ).

intros.
apply (  f_In_list_hold f0 state1 ).
apply ( in_cons   head f0 tail H0)  .
apply (IHpogSubstRel H0 ).
apply H.
Qed.

Lemma wpModImplieswp : forall stmtM    P Q preM preJ listPogJ  stmtJ (assPost : myProp) 
                                                           statePre  stateSP stateAux  ,
                    ( is_wpMod  stmtM Q  preM ) ->
                    ( (evalMyProp ( P  (statePre , stateAux) )) -> ( evalMyProp ( preM  (statePre, stateAux))) ) ->
                   (sp  ( (P (statePre , stateAux) ) , statePre, stateAux,  stmtM   ) (  stmtJ, assPost ,  stateSP, stateAux   ) ) ->  
                   (wpAssume stmtJ Q  preJ listPogJ )  -> 
                                  ((evalMyProp ( P (statePre , stateAux) )  -> ( evalMyProp ( preJ (statePre, stateAux) )) )  /\ 
                                         (forall s , (forall f: Assertion, (In f listPogJ) -> ( evalMyProp (f (s, stateAux) )   )))).
Proof with  auto.


intro stmtM.
induction stmtM; intros until stateAux ; intros HwpMod Himply Hsp  HwpAssume. 


(* skip *)
inversion HwpMod; subst...
inversion Hsp; subst ...
inversion HwpAssume; subst ...
split.
assumption.
intros s  f absurde;
inversion absurde.

(* affect *)
inversion HwpMod; subst...
inversion Hsp; subst ...
inversion HwpAssume; subst ...
split.
unfold update_assert.
unfold update_assert in Himply.
assumption.
intros s f absurde;
inversion absurde.


(* If *)

inversion HwpMod; subst...
inversion Hsp; subst ...
inversion HwpAssume; subst ...
rewrite (extensionality _ _  ( FreezeVarAtState statePre stateAux z ) statePre  ) .
Focus 2.
apply ( semAux5 statePre stateAux z H2). 
rewrite (extensionality _ _  ( FreezeVarAtState statePre stateAux z ) statePre  ) in H12 .
Focus 2.
apply ( semAux5 statePre stateAux z H2). 
rewrite (extensionality _ _  ( FreezeVarAtState statePre stateAux z ) statePre  ) in H13 .
Focus 2.
apply ( semAux5 statePre stateAux z H2). 
simpl in *.

(* prove that  p and c =>  wp ( st1, Q)   *)
assert (hypPandCimplPreT :  ( evalMyProp ((fun s : State*AuxState => 
            let (st, stAux ) := s in   
               p_and   
                             ( p_neq (neval statePre stateAux n) 0)  (P (st , stAux)) ) (statePre , stateAux) ) ) -> 
                             ( evalMyProp ( pre_t ( statePre, stateAux)   )   )   ).
simpl in *.
intro cAndP .
destruct cAndP as [ cond Pholds ].
assert (Himply1 := Himply Pholds ).
destruct Himply1 as [ hypImplThen hypImplElse].
intros.
apply hypImplThen.
intuition.
simpl in hypPandCimplPreT.

(* prove that  p and not c =>  wp ( st2, Q)  *)
assert (hypPandCimplPreF :  ( evalMyProp ((fun s : State*AuxState => 
 let (st, stAux ) := s in   
 p_and   (p_eq (neval statePre stateAux n) 0)  (P (st , stAux)) ) (statePre , stateAux) ) ) -> 
 ( evalMyProp ( pre_f ( statePre, stateAux) ) )  ).
simpl in *.
intro cAndP.
destruct cAndP as [ cond Pholds ].
assert (Himply1 := Himply Pholds ).
destruct Himply1 as [ hypImplThen hypImplElse].
intros.
apply hypImplElse.
intuition.
simpl in hypPandCimplPreF.

assert ( hypIndThen :=  IHstmtM1 
            ( fun _ =>  p_and   ( p_neq(neval statePre stateAux n ) 0) (P (statePre, stateAux)) )
            Q
            pre_t 
            pT
            PT
            st1j 
            assT 
            statePre 
            stateT
            stateAux
            H6
            hypPandCimplPreT 
            H12
            H11
     
  ).

destruct hypIndThen as [ preT preTVC].
assert ( hypIndElse :=  IHstmtM2
            ( fun _ =>  p_and  ( p_eq(neval statePre stateAux n ) 0) (P (statePre, stateAux)) )
            Q
            pre_f 
            pF
            PF
            st2j 
            assF 
            statePre 
            stateF
            stateAux
            H5
            hypPandCimplPreF
            H13
            H14
  ).
destruct hypIndElse as [ preF preFVC].
simpl in *.



split.
intro Pholds.
split.
(*true case of the pre*)
intros cond.
apply preT.
intuition.
(*end of the pre true case*)

(* false case of the pre *)
intros notCond.
apply preF.
intuition.
(* end of the pre false case *)

(* preuve vcs *)
intros s  f h.
assert(h1 :=  in_app_or _ _ _ h).
destruct h1...
(*ON ETAIS LA*)
inversion H15.
subst.
apply (preTVC s  f H).
subst.
rewrite (extensionality _ _  ( FreezeVarAtState statePre stateAux z ) statePre  ) in H15 .

(*fin preuve vcs *)
(* TO BE DONE : need more lemmas about the *)
Focus 3.
(*While *)
inversion HwpMod; subst...
inversion HwpAssume ; subst ...
inversion Hsp; subst ... 
unfold lVar0 .
subst...




split.
intros.
simpl in *.
split.
split.
assumption.
(*get as hypothesis that the invariant holds in the prestate *)
assert ( HinvHoldsInPreState :=   Himply  H). 
destruct HinvHoldsInPreState.
assumption.
trivial.
intros state vc listVc.
destruct listVc.

(*assert that  (  ( P  preState )  and Inv and C and ModCond  => wp (st, I and ModCond and ( P preState ))   ) *)
assert  (      P_Inv_Cond_Mod_implies_wpBody_Of_P_andInv : 
                  evalMyProp (     (p_foralls
                    (fun st_Si : State =>
                     ( p_implies 
                           (P statePre )
                           ( p_implies
                           (p_forallv
                                   (fun x : Var =>
                                    p_implies (p_not (p_in x lVar))
                                        (p_eq (st_Si (progvar x)) (statePre (progvar x)))))
                       (p_implies (invariant st_Si)
                          (p_implies (p_neq (neval st_Si n) 0) (  (pre_st st_Si )   ))))))))).

simpl in *.

intros stIt PInPreState ModCondStIt  invAtStIt CondAtStIt .
(* split. *)
assert ( Himply1 := Himply PInPreState).
destruct Himply1.
destruct H1.
assert (H3 := H2 stIt).
apply H3.
assumption.
assumption.
assumption.
(* assumption. *)
simpl in *.
assert ( P_Inv_Cond_Mod_implies_wpBody_Of_P_andInv1 : forall st : State,
                                            evalMyProp (P statePre) /\ 
                                            (forall var : Var,
                                             ~ In var lVar ->
                                             st (progvar var) =
                                             statePre (progvar var)) /\ 
                                            evalMyProp (invariant st) /\
                                            neval st n <> 0 ->
                                            evalMyProp (pre_st st) ) .
intros.
apply P_Inv_Cond_Mod_implies_wpBody_Of_P_andInv.
destruct H0 ;

assumption;
assumption.
destruct H0.
destruct H1.
assumption.
destruct H0.
destruct H1.
destruct H2.
assumption.
destruct H0.
destruct H1.
destruct H2.
assumption.

(*there exists a weakest precondition *)
assert (exsist_wp_stmtM_inv_modCond_P :=  wpModTotal stmtM
     ( fun st : State =>
  p_and
    ((fun stf : State =>
      p_foralls
        (fun st0 : State =>
         p_and
           (p_forallv
              (fun x : Var =>
               p_implies (p_not (p_in x lVar))
                 (p_eq (stf (progvar x)) (st0 (progvar x))))) (invariant stf)))
       st) (P statePre) )
 ).
elim exsist_wp_stmtM_inv_modCond_P.
intros wpOfStmtM_inv_and_P wpRelStmtM_and_inv_and_P .
clear  exsist_wp_stmtM_inv_modCond_P.
assert ( P_Inv_Cond_ModCond_impl_wpOfStmtM_inv_and_P :=  closedPredinPost
            stmtM 
            (*the closed predicate *)
            (   P statePre ) 
            (*another closed predicate *)
            (  ( fun st : State => 
                                      (p_and 
                                      ( p_and (p_forallv
                                          ( fun x : Var =>
                                                  p_implies (p_not (p_in x lVar))
                                                  (p_eq ( statePre (progvar x))
                                                  (st (progvar x)))))
                                              
                                             (invariant st ) ) 
                                              (p_neq  ( neval st n ) 0 )  ) ) statePre )
                 (*the postcondition Post*)
                 (  fun stf : State =>
                            (p_foralls
                                (fun st : State =>
                                 p_and
                                   (p_forallv
                                      (fun x : Var =>
                                       p_implies (p_not (p_in x lVar))
                                         (p_eq (stf (progvar x))
                                            (st (progvar x)))))
                                   (invariant stf))))
                      (*the wp against Post *)
                     pre_st 
                     (*the wo against Post and P*)
                     wpOfStmtM_inv_and_P            
                     H4
                     wpRelStmtM_and_inv_and_P
).


simpl in *.
assert ( HImplyInd := P_Inv_Cond_ModCond_impl_wpOfStmtM_inv_and_P statePre).
clear P_Inv_Cond_ModCond_impl_wpOfStmtM_inv_and_P.
clear P_Inv_Cond_Mod_implies_wpBody_Of_P_andInv.
assert  (P_Inv_Cond_Mod_implies_wpBody_Of_P_andInv2 :=  
              P_Inv_Cond_Mod_implies_wpBody_Of_P_andInv1  statePre).

simpl in *.
assert (interm :  evalMyProp (P statePre) /\
  ((forall var : Var,
    ~ In var lVar -> statePre (progvar var) = statePre (progvar var)) /\
   evalMyProp (invariant statePre)) /\ neval statePre n <> 0 ->
  evalMyProp (pre_st statePre) ).
intros .
apply P_Inv_Cond_Mod_implies_wpBody_Of_P_andInv2 .
split.
destruct H0.
assumption.
split.
destruct H0.
destruct H1.
destruct H1.
assumption.
split.
destruct H0.
destruct H1.
destruct H1.
assumption.
destruct H0.
destruct H1.
destruct H1.
assumption.
assert ( HImplyInd1 := HImplyInd interm ).
(* apply the induction hypothesis *)
clear P_Inv_Cond_Mod_implies_wpBody_Of_P_andInv2.
clear HImplyInd.
assert (IndApply := 
                      IHstmtM
                      (*the predicate from which the sp predicate is calculated *)
                      ( fun s => ( p_and ( P statePre) 
                               ( p_and
                                      ( p_and 
                                              ( ( p_forallv (fun var : Var =>
                                                       p_implies 
                                                            ( p_not  (  p_in  var lVar ))
                                                            (  p_eq 
                                                                    ( s (progvar var) )  
                                                                    ( statePre (progvar var)) ))))
                                        (invariant s)) 
                                    (p_neq (neval s n )  0   ))) )
                                    
                                    (*the postcondition*)
                                    
  ( fun st : State =>
  p_and
    (p_foralls
       (fun st0 : State =>
        p_and
          (p_forallv
             (fun x : Var =>
              p_implies (p_not (p_in x lVar))
                (p_eq (st (progvar x)) (st0 (progvar x))))) (invariant st)))
    (P statePre) )

                                    (* (fun s : State =>
                                       p_and (p_and (P statePre) (invariant s))
                                        
                                       (p_forallv
                                       (fun v : Var =>
                                       p_implies (p_not (p_in v lVar))
                                       (p_eq (statePre (progvar v)) (s (progvar v)))))) *)
                                      
                                      (*the wp predicate over the stmtM*)
                                      wpOfStmtM_inv_and_P
                                      pI 
                                      PI 
                                      stmtj
                                      assIter 
                                      statePre
                                      stateIter
                                     ( z + 1 )
                                      zPost
                                      wpRelStmtM_and_inv_and_P
                                      HImplyInd1
                                      
).
simpl in *.
(*  may be an useful example 
      generalize (closedPredOutOfQuant _ (fun st =>   ((forall var : Var,
        ~ In var lVar -> statePre (progvar var) = st (progvar var)) /\
       evalMyProp (invariant st)) /\ neval st n <> 0)  H0).
*)


Focus 3.
(*Sequence*)
inversion HwpMod; subst...
inversion Hsp; subst ...
inversion HwpAssume; subst ...
eassert ( HrelWpSpS1 := (relWpSp _ _ _ _ _ _ _ _ _ _ H4 _ H2) )...

eassert(HindS2 := (IHstmtM2 (fun _ => ass1) Q pre_st2 p2 P2 st2j assPost state1 stateSP z1 zPost _ _ _ _))...

assert(Htotale := wpModTotal p2).
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