Require Import semantiqueAux. 
Require Import Ensembles.
Require Import List.
(* Require Import wp. *)
Require Import wpModAux.
Require Import wpAssumeAux.
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
 (sp (Pre , statePre , zPre , stmtm) ( stmtj , Post , statePost,  zPost ))  -> ( (evalMyProp Post )->  (evalMyProp Pre ) ).
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
                                  (AffectAssume z var expr, 
                                  ass
                                 (* (p_and ass  (p_eq ( (update state var (neval  state stateAux expr) ) var )
                                                                (neval  state stateAux expr) ))*), 
                                  update state var (neval  state stateAux expr), 
                                  stateAux)
   | isSpSeq : forall  st1 st2 ass state ass1 state1 ass2 state2  stateAux st1j st2j z  , 
                            ( sp    (ass  , state ,stateAux  ,  st1  )       (st1j, ass1,  state1 , stateAux) ) ->
                            ( sp    (ass1, state1, stateAux, st2  ) (  st2j, ass2, state2, stateAux ) ) -> 
                            ( sp    (ass, state,  stateAux, (SeqInd  Invariant_m z st1 st2) ) 
                                      ( ( SeqAssume z st1j st2j ), ass2, state2, stateAux  ))
   | isSpIf : forall   expB st1 st2 ass state assT assF  stateT stateF stateAux  st2j st1j z ,
                           (*  ( forall v : Var ,   (stateAux (AuxName v z) )  = (state v) ) -> *) 
                            (sp  (  (* p_and  ( p_forallv  ( fun v =>  ( p_eq  (stateAux (AuxName v z) ) (state v))) ) *)
                                        ( p_and  ( p_neq  ( neval (*  (FreezeVarAtState state stateAux z) *) state stateAux   expB  )  0 ) ass   ), 
                                        state (* (FreezeVarAtState state stateAux z)  *) ,  
                                        stateAux, 
                                        st1 
                                    )  
                                   (  st1j, assT, stateT, stateAux  ) 
                            ) ->
                            (sp  (  (* p_and  ( p_forallv  ( fun v =>  ( p_eq  (stateAux (AuxName v z) ) (state v))) ) *) 
                                     ( p_and   ( p_eq ( neval (* (FreezeVarAtState state stateAux z) *)  state   stateAux  expB  )  0 )   ass  ), 
                                     state (*   (FreezeVarAtState state stateAux z) *),  
                                     stateAux, 
                                     st2 )   
                                   (  st2j, assF, stateF, stateAux ) 
                            ) ->    
                            (sp  
                                  ( ass, 
                                     state,  
                                     stateAux,
                                     ( IfInd Invariant_m z expB  st1 st2) )  
                                   ( ( IfAssume z  (* ( state (FreezeVarAtState state stateAux z) , stateAux) *)  expB  st1j   st2j  ),  
                                     p_or assF  assT , 
                                     ( stateAtIf stateAux state stateF stateT expB) ,
                                     stateAux
                                   ) 
                            )
  | isSpwhile : forall  expB stmt ass state inv lVar stmtj assIter stateIter (* auxStateIterStart  auxStateLoopEnd
    auxStateEndIter *) auxState zBody z  ,
                           ( isFresh z  ass )    ->
                           ( isFresh z ( p_and (inv (state, auxState) ) ( (p_eq (neval state auxState  expB)  0 ))) ) ->
                           (* the following condition is redundant wrt with the previous but suitable for the proof of the lemma p -> wp(st , sp(st, P)) *)
                           ( isFresh z  (inv (state, auxState ) ) )->
                           ( isFresh z  ( p_eq (neval state auxState  expB) 0 ) )->
                           ( isStmtIndMod stmt zBody) ->
                           (forall v : Var , (~ In v lVar) ->  (* getVarValAtState  z v *) (auxState (AuxName v z )) = (state v) )->
                           let newInv :=  (fun st : State*AuxState =>
                                                           let (s, sAux) :=  st in
                                                           ( p_and (p_and ass  ( inv (s , sAux) ) )  
                                                                        ( p_forallv ( fun v: Var => (p_implies (p_not ( p_in  v lVar))    
                                                                                                            ( p_eq  (auxState (AuxName v z )) 
                                                                                                            ( neval s sAux (nvar v) ))))))) in
                                                                                            
                           (evalMyProp ass -> evalMyProp (inv (state, auxState))) -> 
                            (*commented because otherwise there will be a contradiction with the next condition, because this
                          states that the condition is true and the other states that the condition is not true in the same state *)
                           (* evalMyProp ( p_and 
                                                 (p_eq ( neval  ( state (FreezeVarAtState state auxState z)  (* stateAtLoop  state auxState  z lVar *)  auxState   expB )  0 ) 
                                                 ( inv   ( (* stateAtLoop  state auxState z lVar *) (FreezeVarAtState state auxState z)  ,  auxState) ) 
                                                ) -> *)  
			(*the interpretation of the auxiliary vars auxStateIterStart is such that the strongest postcondition predicate also holds*)
		          ( evalMyProp  
			      (p_and (p_and ass ( inv ( (FreezeVarAtState state auxState z) (* stateAtLoop  state auxState zBody lVar *) , auxState ) ))   
                                                ( ( p_eq ( neval  (FreezeVarAtState state auxState z)  (* stateAtLoop  state auxState zBody lVar *)  auxState expB )  0) )) 
			   ) ->
                           (*CONSTRUCT THE SUBSTITUTION lIST*)
			  (* ( constructModVarSubstList lVar z ( stateAtLoop  state stateAux z lVar )  lVarSubst ) ->  *)
                          (sp  ( (p_and (  p_and ass ( inv ( (FreezeVarAtState state auxState z) (* stateAtLoop  state auxState zBody lVar *) , auxState ) ))   
                                                   ( p_not( p_eq ( neval (FreezeVarAtState state auxState z)  (* stateAtLoop  state auxState zBody lVar *)  auxState expB )  0) )) ,
                                    (FreezeVarAtState state auxState z)  , 
                                    auxState,
                                    stmt
                                  ) 
                                 (
                                   stmtj, 
                                   assIter, 
                                   stateIter ,
                                   auxState
                                 ) )  -> 
                           ( sp    ( ass,  
                                       state, 
                                       auxState,
                                       WhileInd  Invariant_m z expB ( inv_m  inv lVar )  stmt 
                                     )                                                   
                                     ( WhileAssume z (inv_j newInv) ( (FreezeVarAtState state auxState z) (* stateAtLoop  state auxState z lVar *), auxState )  expB stmtj   ,                                    
                                            p_and  ( 
                                               p_and (  inv ( (FreezeVarAtState state auxState z) (* stateAtLoop  state auxState z lVar *) , auxState ) ) ass )
                                                          (  p_eq  ( neval (FreezeVarAtState state auxState z) (* stateAtLoop state auxState  z lVar *)  auxState expB )  0 ), 
                                             (FreezeVarAtState state auxState z) , 
                                             auxState
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
simpl in *.
(* unfold update .
split. intuition.
case ( vareq v v ).
reflexivity. *) 
(*if *)
inversion HStrongestPost; subst ...
assert ( HInd1 := IHstmtM1 
                              st1j 
                             (* (FreezeVarAtState state1 stateAux2 z)  *)
                             state1
                              stateT
                              stateAux2
                              stateAux2
                              (fun _  =>
                                          (p_and (p_neq (neval state1 stateAux2 n) 0) 
                                                      (Pre (state1,  stateAux2))))
                              assT ).

 rewrite
 ( applicationToConstFuncts ( p_and (p_neq (neval state1 stateAux2 n) 0) (Pre (state1, stateAux2)) ) state1 ) in 
 HInd1.
(* rewrite <- (progExprEvalProp1 stateAux) in H1. *)

assert ( HInd1Simpl :=  HInd1 H1 ).
simpl in *.
clear HInd1.
assert ( HInd2 := IHstmtM2
                              st2j 
                              state1
                              (* (FreezeVarAtState state1 stateAux2 z) *)
                              stateF
                              stateAux2
                              stateAux2
                              (fun _  =>
                                          (p_and (p_eq (neval state1 stateAux2 n) 0) 
                                                      (Pre (state1,  stateAux2))))
                              assF
                              ).

 rewrite
 ( applicationToConstFuncts ( p_and (p_eq (neval state1 stateAux2 n) 0) (Pre (state1, stateAux2)) ) state1 ) in  HInd2.
(* rewrite <- (progExprEvalProp1 stateAux) in H10. *)
assert ( HInd2Simpl :=  HInd2 H11 ).
simpl in *.
clear HInd2.
assert (thiersExclu := classic  ((neval state1  stateAux2 n) = 0 ) ).
destruct thiersExclu.
assert ( assertAssF  := HInd2Simpl (conj H HPreHolds  )   ).
left.
assumption.
assert ( assertAssF  := HInd1Simpl   (conj H HPreHolds  )  ).
right.
assumption.


(*while *)

inversion HStrongestPost. 
unfold newInv in *.

subst ...
simpl in *.
intros.
destruct H17.
split .
split.
destruct H.
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

assert(Hfalse := (IHstmtM2  _ _ _  (* FreezeVarAtState statePre stateAuxPost z*) statePre   _  _ stateAuxPost H11 H)).
simpl in Hfalse.  intuition. 
assert(Htrue := (IHstmtM1 _ _ _ _ _ _  stateAuxPost H1 H)).
simpl in Htrue .  intuition.

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
Axiom etaExpansion: forall  (A B : Set) ( a : A ->  B) ,   a = (fun c : A => a c).

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
(* rewrite (semAux3  statePre stateAuxPost n z H2 ) in H13. *) 
(* rewrite (extensionality _ _  ( FreezeVarAtState statePre stateAuxPost z ) statePre  ) in H13. *) 
(* Focus 2. *)
(* apply ( semAux5 statePre stateAuxPost z H2). *)
simpl in *.
assert ( hypIndThen1 := hypIndThen H1  ).


(*get some hyps for the  else case*)
assert ( HypWpElse : (  neval statePre stateAuxPost n = 0 /\ evalMyProp (Pre ( statePre, stateAuxPost ))  )-> evalMyProp (pre_f (statePre, stateAuxPost)) ).
intros.
destruct H.
assert ( hypWpImp := hypWP_Implied H0 ).
destruct hypWpImp...
(*HypWpElse proven *)
assert (hypIndElse := ( IHstmtM2 st2j   pre_f  ( fun s =>let (st, stAux ) := s in (  p_and (p_eq (neval st stAux n)  0 )  ( Pre (st, stAux))  ))  Post assF  statePre stateF  stateAuxPost stateAuxPost H5 HypWpElse ) )...

(* rewrite (semAux3 statePre stateAuxPost n z H2 ) in H14.
rewrite (extensionality _ _  ( FreezeVarAtState statePre stateAuxPost z ) statePre  ) in H14.
Focus 2.
apply ( semAux5 statePre stateAuxPost z H2). *)

simpl in *.
assert ( hypIndElse1 := hypIndElse H13  ).
assert(hStrF := (spStrongerThanPre _ _ _ _ _ _ _ _  H13)).
assert(hStrT := (spStrongerThanPre _ _ _ _ _ _ _ _  H1)).
 simpl in hStrT, hStrF.
unfold stateAtIf.
case (Z_eq_dec (neval statePre stateAuxPost n) 0 ) .

intro cond.
simpl.
rewrite <- (etaExpansion _ _ stateF).
destruct SPholds as [ assFProof | assTProof ].
apply hypIndElse1.
assumption.
assert  (Haha := hStrT assTProof ).
destruct Haha.
contradiction.


intro notcond.
simpl.
rewrite <- (etaExpansion  _ _ stateT).
destruct SPholds as [ assFProof | assTProof ].

assert  (Haha := hStrF assFProof ).
destruct Haha.
contradiction.
apply hypIndThen1.
assumption.

(* while *)
inversion hypSP. 
unfold newInv in *. 
clear newInv.
subst...
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
unfold FreezeVarAtState.
trivial.
(*apply h5.*)
assumption.
assumption.
(*assumption. *)


(* Seq *)
inversion hypSP; subst...
inversion hypWP; subst...
intros.
assert(Hind1 := IHstmtM1 st1j  _  _  _ _ _ _ _ _    H6 hypWP_Implied   H1 ) .
assert(Hind2 := IHstmtM2 st2j  _ (fun _ => ass1) _ _ _ _ _ _   H5 Hind1 H10)...

Qed.


(*a condition that the loop invariants are correct must be added  *)
 Axiom  Pre_implies_wp_of_sp : forall stmtM stmtJ ( PRE : myProp ) 
sPost statePre statePost auxState   wPre , 
  ( sp ( PRE   , statePre , auxState, stmtM) ( stmtJ,  sPost , statePost,  auxState  ) )->  
  ( forall z loopBody loopCond loop invariant lVar invPreserv, 
     (loop  = WhileInd Invariant_m  z loopCond   (inv_m invariant lVar ) loopBody )  ->
     ( is_wpMod loopBody  ( fun st   => let (s, sAux) := st in
                                                   p_and    (p_forallv (fun x => (p_implies 
                                                                                (p_not (p_in x lVar)) 
                                                                                (p_eq ( getVarValAtState z x ) ( s  x )))))
                                                                      ( invariant st ) )
                                                                      invPreserv )     ->
     (forall s ,  (evalMyProp ( invariant (s ,auxState  ) ) 
                       /\ ( forall v , ~ (In v lVar )    -> (s v) = (getVarValAtState z v )  ) 
    )  -> evalMyProp ( invPreserv (s, auxState ) ))
 )   ->
  ( is_wpMod  stmtM ( fun s =>  sPost)  wPre ) -> 
  (   (evalMyProp  PRE  ) -> ( evalMyProp ( wPre  (statePre , auxState  ) ) )  ) .
(* 
Proof with auto.
intro stmtM. induction stmtM; intros until wPre;  intro SP;  intro invariantsCorrect ; intro WP.

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

assert ( IHypThen1 :=  (IHstmtM1
                                        st1j 
                                        (   p_and (p_neq (neval statePre  auxState n) 0) PRE )   
                                        assT   
                                        statePre  
                                        stateT 
                                        auxState 
                                        _ 
                                        H2 
                                        invariantsCorrect  
                                        wpAssT)).
 (* exact H1. *)

assert ( Then_impl_ThenOrElse :  forall state ,
                       ( evalMyProp ( (fun _  => assT)  ( state, auxState ) ) ) ->
             (  evalMyProp ( (fun s : State * AuxState  => p_or assF assT) (state, auxState ) ) )    ).
intros.
simpl in *.
right. 
assumption.
assert ( applyMonotThenInStatePre := ( wpModMon 
                                        stmtM1  
                                        ( fun s => assT) 
                                        (fun s => (  p_or assF assT)  ) 
                                        auxState 
                                        wpExists 
                                        pre_t  
                                        wpAssT 
                                        H8    
                                        Then_impl_ThenOrElse  
                                        ) ).
simpl in *.
intro cond.

assert ( wpExistsHoldsInState0 :=  IHypThen1   (conj cond H)  ).
(* assumption. *)
simpl in *.
apply (applyMonotThenInStatePre statePre   ).
unfold State, AuxState.
(* rewrite <- (semAux4 statePre auxStatePost wpExists z H3). *) 
assumption.


(*else case *)
assert ( existsWpElse := wpModTotal  stmtM2 (fun s  => assF)  ).
elim existsWpElse. 
intro wpExists. 
intro wpAssF.

assert ( IHypElse1 :=  (IHstmtM2   
                                        st2j 
                                        (  p_and (p_eq (neval  statePre  auxState n) 0)   PRE  )  
                                        assF    
                                        statePre   
                                        stateF 
                                        auxState  
                                        _
                                        H11
                                        invariantsCorrect  
                                        wpAssF  )).
(* exact H11. *) 
assert ( Else_impl_ThenOrElse :  forall state ,
                       ( evalMyProp ( (fun _  => assF)  ( state, auxState ) ) ) ->
             (  evalMyProp ( (fun s : State * AuxState  => p_or assF assT) (state, auxState ) ) )    ).
intros.
simpl in *.
left. 
assumption.



assert ( applyMonotElseInStatePre := ( wpModMon 
                                        stmtM2 
                                        ( fun s => assF) 
                                        (fun s => (  p_or assF assT)  ) 
                                        auxState 
                                        wpExists 
                                        pre_f  
                                        wpAssF 
                                        H7   
                                        
                                        Else_impl_ThenOrElse  
                                        ) ).
simpl in *.
intro notCond.
(* rewrite <- ( semAux3 statePre auxStatePost n z) in notCond. *)
assert ( wpExistsHoldsInState0 :=  IHypElse1   (conj notCond H)  ).
(* assumption. *)
simpl in *.
apply (applyMonotElseInStatePre statePre   ).
unfold State, AuxState.
(* rite <- (semAux4 statePre auxStatePost  wpExists z H3). *)
assumption.



(* HERREERE - CONTINUE HERRERERRER *)

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

Axiom wpIsFunction : forall stmt P wp1 wp2 , 
  ( is_wpMod  stmt P wp1  )   ->
( is_wpMod  stmt P wp2  )   -> wp1 = wp2.

Lemma closedPredInPost : 
forall stmtM (closed : Assertion )  wp1 wp2 post  stateAux ,
  ( is_wpMod  stmtM post wp1  )   ->
  forall STATE, 
( ( is_wpMod  stmtM (fun s => let (st, stAux) := s in  p_and ( post ( st, stAux) ) (closed (STATE, stateAux)) ) wp2 )    ->
  forall state , (  ( evalMyProp  (wp1 (state, stateAux) )) /\ ( evalMyProp  (closed (STATE, stateAux)) )  ) ->
   ( evalMyProp  (  wp2  (state, stateAux))) ).
Proof .
intros stmt; induction stmt;
intros until stateAux;
intros wp1H STATE wp2H state wp1AndClosed;

(* skip *)
inversion wp1H; subst...
inversion wp2H; subst ...
simpl in *.
trivial.


(*assign *)
inversion wp1H; subst...
inversion wp2H; subst ...
simpl in *.
trivial.


(*if  *)
inversion wp1H; subst...
inversion wp2H; subst ...
simpl in *.
destruct wp1AndClosed as [[ trueCase  falseCase]  closedHolds ].
split .
intros cond.
assert ( trueCase1  :=  trueCase cond).
apply ( IHstmt1 closed _ _ _  stateAux H6 STATE H11  state (conj trueCase1 closedHolds)) .

intros cond.
assert ( falseCase1  :=  falseCase cond).
apply ( IHstmt2 closed _ _ _  stateAux H5 STATE H10 state  (conj falseCase1 closedHolds)) .

(*while   *)
inversion wp1H; subst...
inversion wp2H; subst ...
simpl in *.
split.
intuition.
split.
intuition.
split.
assert (uniqueWP := wpIsFunction 
                     stmt    
                     (fun st : State * AuxState =>
                     let (s, sAux) := st in
                     p_and
                     (p_forallv
                     (fun x : Var =>
                     p_implies (p_not (p_in x lVar))
                     (p_eq (sAux (AuxName  x z) ) (s x)))) (invariant st) )
                     pre_st
                     pre_st1
                     H5
                     H9 (*H12*)
). 
intros.
rewrite <-    uniqueWP.
intuition.
intuition.

(*sequence *)
inversion wp1H; subst...
inversion wp2H; subst ...
simpl in *...
assert ( exsistsWp := wpModTotal stmt1  ( fun s : State * AuxState =>
     let (st, stAux) := s in p_and (pre_st0 (st, stAux)) (closed (STATE, stateAux) )) ).
destruct exsistsWp.
assert (H2:=  IHstmt1 closed wp1  x  pre_st0 stateAux  H7 STATE H _ wp1AndClosed ).
assert(H1 := IHstmt2 closed pre_st0 pre_st1 post  stateAux H6 STATE H8 ).
assert (mon := wpModMon stmt1 
             ( fun s : State * AuxState =>
             let (st, stAux) := s in 
             p_and (pre_st0 (st, stAux)) 
                        (closed (STATE, stateAux) )  ) 
             pre_st1  
             stateAux 
             x 
             wp2
             H
             H9
             H1
             state 
             H2).
assumption.
Qed.

(*  this holds from the relation between wp and sp)
Lemma forall state stateAux Pre SP Post WP stmtM stmtJ , 
(sp ( ( P ( statePre, stateAux) ), statePre, stateAux, stmtM ) (stmtJ, SP , statePost, stateAux ) ) ->
( is_wpMod stmtM Post WP ) ->
( evalMyProp ( WP (statePre, stateAux)) ) ->
( evalMyProp ( P (statePre , stateAux)) ) ->
( ( evalMyProp ( SP( statePre, stateAux) ) )  /\  (( evalMyProp ( SP( statePre ,stateAux) ) ) ->   ( evalMyProp Post (s)  )   )
*)

Axiom EqPostInWp : forall P1 P2 P3 stmt WP ,
(is_wpMod stmt ( fun state =>  let (s , sA) := state in 
                                   ( p_and ( p_and P1 ( P2 (s, sA) )  ) ( P3 (s, sA) )) ) WP ) ->
(is_wpMod stmt ( fun state =>  let (s , sA) := state in 
                                  (p_and (  p_and ( P3 (s, sA) )  ( P2 (s, sA) )) P1) ) WP ).



Axiom badEquiv : forall stmtj lVar ( statePre : State ) z stateAux pI PL invariant P ,
( wpAssume stmtj
    (fun stat : State * AuxState =>
     let (state, auxState) := stat in
     p_and
       (p_and
          (p_forallv
             (fun v : Var =>
              p_implies (p_not (p_in v lVar))
                (p_eq (auxState (AuxName v z)) (state v))))
          (invariant (state, auxState))) (P (statePre, stateAux))) pI PL )
 =
( wpAssume stmtj
    (fun st : State * AuxState =>
     let (s, sAux) := st in
     p_and (p_and (P (statePre, stateAux)) (invariant (s, sAux)))
       (p_forallv
          (fun v : Var =>
           p_implies (p_not (p_in v lVar))
             (p_eq (stateAux (AuxName v z)) (s v))))) pI PL ).  

Lemma wpModImplieswp : forall stmtM    P Q preM preJ listPogJ  stmtJ (assPost : myProp) statePre  stateSP ( stateAux : AuxState) ,
                    ( is_wpMod  stmtM Q  preM ) ->
                   ( (evalMyProp ( P  (statePre , stateAux) )) -> ( evalMyProp ( preM  (statePre, stateAux))) ) -> 
	(* forall state , ( (evalMyProp ( P  (state , stateAux) )) -> ( evalMyProp ( preM  (state , stateAux))) ) -> *)            
        (sp  ( (P (statePre , stateAux) ) , statePre, stateAux,  stmtM   ) (  stmtJ, assPost ,  stateSP, stateAux   ) ) ->  
                   (wpAssume stmtJ Q  preJ listPogJ )  -> 
                                  ((evalMyProp ( P (statePre , stateAux) )  -> ( evalMyProp ( preJ (statePre, stateAux) )) )  /\ 
                               forall s,  (forall   f: Assertion, (In f listPogJ) -> ( evalMyProp (f (s , stateAux) )   ))).
Proof with  auto.


intro stmtM.
induction stmtM; intros until stateAux ; intros HwpMod Himply Hsp  HwpAssume. 


(* skip *)
inversion HwpMod; subst...
inversion Hsp; subst ...
inversion HwpAssume; subst ...
split.
apply Himply.
intros s  f absurde;
inversion absurde.

(* affect *)
inversion HwpMod; subst...
inversion Hsp; subst ...
inversion HwpAssume; subst ...
split.
unfold update_assert.
unfold update_assert in Himply.
apply Himply.
intros s f absurde;
inversion absurde.


(* If *)

inversion HwpMod; subst...
inversion Hsp; subst ...
inversion HwpAssume; subst ...
(* rewrite (extensionality _ _  ( FreezeVarAtState statePre stateAux z ) statePre  ) .
Focus 2.
apply ( semAux5 statePre stateAux z H2). 
rewrite (extensionality _ _  ( FreezeVarAtState statePre stateAux z ) statePre  ) in H12 .
Focus 2.
apply ( semAux5 statePre stateAux z H2). 
rewrite (extensionality _ _  ( FreezeVarAtState statePre stateAux z ) statePre  ) in H13 .
Focus 2.
apply ( semAux5 statePre stateAux z H2). *)  
simpl in *.

(* prove that  p and c =>  wp ( st1, Q)   *)
assert (hypPandCimplPreT :  (  ( evalMyProp ( 
               p_and   
                             ( p_neq (neval statePre stateAux n) 0)  (P (statePre , stateAux)) )  ) ) -> 
                             ( evalMyProp ( pre_t ( statePre, stateAux) ) ) )  .
simpl in *.
intros   cAndP .
destruct cAndP as [ cond Pholds ].
assert (Himply1 := Himply  Pholds ).
destruct Himply1 as [ hypImplThen hypImplElse].
intros.
apply hypImplThen.
intuition.
simpl in hypPandCimplPreT.

(* prove that  p and not c =>  wp ( st2, Q)  *)
assert (hypPandCimplPreF :  (  (evalMyProp ( 
 p_and   (p_eq (neval statePre stateAux n) 0)  (P (statePre , stateAux)) )  ) ) -> 
 ( evalMyProp ( pre_f ( statePre, stateAux) ) )  ).
simpl in *.
intros  cAndP.
destruct cAndP as [ cond Pholds ].
assert (Himply1 := Himply Pholds ).
destruct Himply1 as [ hypImplThen hypImplElse].
intros.
apply hypImplElse.
intuition.
simpl in hypPandCimplPreF.

assert ( hypIndThen :=  IHstmtM1 
            ( fun s  => let (st, stAux)  := s in 
                             p_and   ( p_neq(neval st stAux n ) 0) (P (st, stAux)) )
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
     (*       H12
            H9
     *)
  ).

simpl in hypIndThen.
assert ( hypIndThen1 :=  hypIndThen H1 H9 ).
destruct hypIndThen1 as [ preT preTVC].
assert ( hypIndElse :=  IHstmtM2
              ( fun s  => let (st, stAux)  := s in 
                             p_and   ( p_eq(neval st stAux n ) 0) (P (st, stAux)) )
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
          (*  H13
            H14 *)
  ).
simpl in hypIndElse.
assert ( hypIndElse1 :=  hypIndElse H12 H10 ).
destruct hypIndElse1 as [ preF preFVC].
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

(*fin preuve vcs *)
(* TO BE DONE : need more lemmas about the *)

(*While *)
inversion HwpMod; subst...
inversion Hsp; subst ... 
inversion HwpAssume ; subst ...
subst...

split.

simpl in *.
intros. intuition.
intros state f assInList.
destruct assInList.
subst.
rewrite  <-   H .
simpl in *.

assert ( hyp1forInd :   ( evalMyProp (P (statePre, stateAux)) -> 
         
          (forall var : Var, ~ In var lVar -> ( stateAux  (AuxName var z) ) = (FreezeVarAtState statePre stateAux z) var) ->
          evalMyProp (invariant ( (FreezeVarAtState statePre stateAux z ) , stateAux)) ->
          neval (FreezeVarAtState statePre stateAux z )  stateAux n <> 0 -> 
             evalMyProp (pre_st ((FreezeVarAtState statePre stateAux z) , stateAux)) /\   
             evalMyProp (P (  statePre , stateAux)))
).
intros  Pholds   varCond invHolds  condHolds .

assert ( Himply1 := Himply   Pholds ).
destruct Himply1 as [ c1 [c2 [c3 c4]] ].
split.
apply c3.
assumption.
assumption.
assumption.
assumption.
simpl in H.
subst.
intros.
assert ( existsWp :=   
wpModTotal 
stmtM
( fun stat : State * AuxState =>
   let (state, auxState ) := stat in 
    p_and
 ( ( fun st : State * AuxState =>
   let (s, sAux) := st in
   (p_and 
      ( p_forallv
           (fun v : Var =>
            p_implies (p_not (p_in v lVar))
              (p_eq ( sAux ( AuxName v z )) (s v))))
  (invariant (s, sAux)))) ( state , auxState ))
   (P (statePre, stateAux)) 
) ). 

destruct existsWp.



assert ( closedPred :=  closedPredInPost 
                                      stmtM 
                                      P    
                                      pre_st  
                                      x 
                                      ( fun st : State * AuxState =>
                                      let (s, sAux) := st in
                                      p_and
                                      ( p_forallv
                                      (fun v : Var =>
                                      p_implies (p_not (p_in v lVar))
                                      (p_eq ( sAux ( AuxName v z )) (s v)))) 
                                      (invariant st )
                                      )
                                    stateAux

                                    H5
                                    statePre  
                                    H0
).


intros.

assert ( hypInd2 := 
(evalMyProp ( P (statePre, stateAux))) /\ 
( forall var: Var , ~ In var lVar ->  (stateAux (AuxName var z)) =  (statePre var) ) /\ 
evalMyProp ( invariant (FreezeVarAtState statePre stateAux z, stateAux )) 


).
assert ( HInd2 : ( evalMyProp (P (statePre, stateAux)) ->      
          (forall var : Var, ~ In var lVar -> ( stateAux  (AuxName var z) ) = (FreezeVarAtState statePre stateAux z) var) ->
          evalMyProp (invariant ( (FreezeVarAtState statePre stateAux z ) , stateAux)) ->
          neval (FreezeVarAtState statePre stateAux z )  stateAux n <> 0 -> 
     (evalMyProp (x ( (FreezeVarAtState statePre stateAux z ) , stateAux ))))).
intros.
apply closedPred.
apply hyp1forInd.
assumption.
assumption.
assumption.
assumption.
(* assert ( wpSimpl := 
(EqPostInWp (P (statePre, stateAux)) 
                        ( invariant  ) 
                        ( fun state => let (s, sAux) := state in
                              p_forallv  ( fun v: Var  => p_implies ( p_not (p_in v lVar  ))
                                                                         (p_eq (sAux (AuxName v z) ) (s v)  ) )  
                        ) stmtM x H9)) . 
*)

assert ( trick :=  badEquiv stmtj lVar statePre z stateAux pI PL invariant P  ) .
assert ( wellFormedAppl : evalMyProp
    ((fun _ : State * AuxState =>
      p_and
        (p_and (P (statePre, stateAux))
           (invariant (FreezeVarAtState statePre stateAux z, stateAux)))
        (p_not
           (p_eq (neval (FreezeVarAtState statePre stateAux z) stateAux n) 0)))
       (FreezeVarAtState statePre stateAux z, stateAux)) ->
  evalMyProp (x (FreezeVarAtState statePre stateAux z, stateAux)) ).
simpl .
intros.
apply HInd2.
intuition.
intuition.
intuition.
intuition.

assert ( Ind := 
      IHstmtM  
      ( fun _ => p_and 
     ( p_and 
             (P (statePre, stateAux))
             ( invariant ((FreezeVarAtState statePre stateAux z ) , stateAux ))
             )
             ( p_not ( p_eq ( neval (FreezeVarAtState statePre stateAux z ) stateAux n ) 0 ))
             )

      _ 
      x 
      pI
      PL
      _ 
      assIter 
      (FreezeVarAtState statePre stateAux z ) 
      stateIter 
      stateAux 
      H0 
      wellFormedAppl
      H19 ).
clear HInd2.
rewrite  trick in Ind.
assert ( Ind1 := Ind H9).
H9  HInd2).
(*faire une axiom qui dit que wpAssume applique a l'uin et a l'autre cas c'est la meme chose *)

Qed.

