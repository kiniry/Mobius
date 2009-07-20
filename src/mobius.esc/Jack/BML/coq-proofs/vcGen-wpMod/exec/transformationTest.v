Require Import semantiqueAux. 
Require Import Ensembles.
Require Import List.
(* Require Import wp. *)
Require Import wpModAux.
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
 | SkipAssume : Z -> stmtJAssume
 |  AffectAssume : Z -> Var -> NumExpr -> stmtJAssume
(* | Assume  : State -> Assertion -> stmtJAssume*)
 | SeqAssume : Z -> stmtJAssume -> stmtJAssume -> stmtJAssume 
 | IfAssume : Z -> NumExpr -> stmtJAssume  ->  stmtJAssume  -> stmtJAssume  
(*note that the second argument is a list of pairs of prog variables and auxiliary variables, but we do not see the difference as both variables are from the type Var *)
 | WhileAssume : Z -> Invariant_j ->  State -> NumExpr ->  stmtJAssume  ->  stmtJAssume  .

(*operational semantics *)
Inductive execStmtAss : State -> stmtJAssume    -> State -> Set :=
| execSkipAss : forall s z, execStmtAss s (SkipAssume z) s
| execAffectAss : forall s v exp sAux z ,   
            execStmtAss s (AffectAssume  z v exp) (update s v (neval s sAux exp))
| exectBsIfTrue: forall s s' cond stThen stElse sAux z, 
           neval s sAux cond <> 0 -> 
           execStmtAss s stThen s'  ->
           execStmtAss s (IfAssume z cond stThen stElse) s'
| exectBsIfFalse: forall s s' cond stThen stElse sAux z , 
           neval s sAux cond = 0 -> 
           execStmtAss s stElse s'  ->
           execStmtAss s (IfAssume z cond stThen stElse) s'
| execBsWhileFalse: forall inv listSubst  cond  stmt  s sAux z , neval s sAux cond = 0 -> 
          execStmtAss s (WhileAssume z (inv_j inv)  listSubst  cond  stmt) s
| execBsWhileTrue: forall inv   substState cond stmt   s s' s'' sAux z, 
          neval s sAux cond <> 0 -> 
          (execStmtAss s stmt s') -> 
          (execStmtAss s' (WhileAssume  z (inv_j inv) substState  cond   stmt) s'') ->
          (execStmtAss s  (WhileAssume  z (inv_j inv) substState  cond   stmt) s'') 
| execBsSeq: forall s s' s'' st1 st2 z, 
          execStmtAss s st1 s' ->
          execStmtAss s' st2 s'' -> 
          execStmtAss s (SeqAssume z st1 st2) s''.

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
 fun v: Var => if ( Zeq  ( neval state   auxState expB  )  0 )
         then (neval stateF auxState  (nvar v) ) 
         else  ( neval stateT auxState (nvar v ))
.

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
                            (sp  (  ( p_and  ( p_neq  ( neval state stateAux   expB  )  0 ) ass   ), state,  stateAux, st1 )  
                                   (  st1j, assT, stateT, stateAux  ) ) ->
                            (sp  ( 
                                     ( p_and   ( p_eq ( neval state  stateAux  expB  )  0 )   ass  ), state,  stateAux, st2 )   
                                     (  st2j, assF, stateF, stateAux ) 
                                   ) ->    
                            (sp  
                                  ( ass, 
                                     state,  
                                     stateAux,
                                     ( IfInd Invariant_m z expB  st1 st2) )  
                                   ( ( IfAssume z expB  st1j   st2j  ),  
                                     p_or assF  assT , 
                                     ( stateAtIf stateAux state stateF stateT expB) ,
                                     stateAux
                                   ) 
                            )
  | isSpwhile : forall  expB stmt ass state inv lVar stmtj assIter stateIter stateIterStart  stateLoopEnd  auxState  z  ,
                           ( isFresh z  ( fun st => ass) )    ->
                           ( isFresh z (fun st => let (s , sAux ) := st in (p_and (inv st) ( (p_eq (neval s auxState  expB)  0 ) )))) ->
                           (* the following condition is redundant wrt with the previous but suitable for the proof of the lemma p -> wp(st , sp(st, P)) *)
                           ( isFresh z  inv )->
                           ( isFresh z ( fun st =>  let (s , sAux ) := st in  ( p_eq (neval s auxState  expB) 0 ) ) ) ->
                           let newInv :=  (fun st : State*AuxState =>
                                                           let (s, sAux) :=  st in
                                                           ( p_and (p_and ass  ( inv (s , sAux) ) )  
                                                                        ( p_forallv ( fun v: Var => (p_implies (p_not ( p_in  v lVar))    
                                                                                                            ( p_eq ( neval state auxState (nvar v ) ) 
                                                                                                            ( neval s sAux (nvar v) ))))))) in
                                                                                            
                           (evalMyProp ass -> evalMyProp (inv (state, auxState))) -> 
                           (evalMyProp ( p_and 
                                                 (p_eq ( neval  ( stateAtLoop  stateLoopEnd auxState z lVar )  auxState  expB )  0 ) 
                                                 ( inv   ( ( stateAtLoop  stateLoopEnd auxState z lVar ),  auxState) ) 
                                                ) 
                           )  ->
                           (*CONSTRUCT THE SUBSTITUTION lIST*)
			  (* ( constructModVarSubstList lVar z ( stateAtLoop  state stateAux z lVar )  lVarSubst ) ->  *)
                          (sp  ( (p_and (  p_and ass ( inv ( ( stateAtLoop  stateIterStart auxState z lVar ) , auxState) ))   
                                                   ( p_not( p_eq ( neval   ( stateAtLoop  stateIterStart auxState z lVar )  auxState expB )  0) )) ,
                                    ( stateAtLoop  stateIterStart auxState z lVar )  , 
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
                                     ( WhileAssume z (inv_j newInv) ( stateAtLoop  stateLoopEnd auxState z lVar )  expB stmtj   ,                                    
                                            p_and  ( 
                                               p_and (  inv ( ( stateAtLoop  stateLoopEnd auxState z lVar ) , auxState) ) ass )
                                                          (  p_eq  ( neval ( stateAtLoop  stateLoopEnd auxState z lVar )  auxState expB )  0 ), 
                                             ( stateAtLoop  stateLoopEnd auxState z lVar )  ,
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
forall stmtM stmtJ state1 state2 stateAux (Pre : Assertion  ) ( SP : myProp ) , 
  (sp  ( (Pre  (state1, stateAux) ) , state1, stateAux, stmtM   ) ( stmtJ , SP ,  state2, stateAux  ) )  ->
( evalMyProp  (Pre (state1, stateAux ) ) -> ( evalMyProp SP)) .  
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
                              state1 
                              stateT
                              stateAux
                              (fun s => p_and (p_neq (neval state1 stateAux n) 0) (Pre (state1,  stateAux))) 
                              assT ).

 rewrite
 ( applicationToConstFuncts ( p_and (p_neq (neval state1 stateAux n) 0) (Pre (state1, stateAux)) ) state1 ) in 
 HInd1.
(* rewrite <- (progExprEvalProp1 stateAux) in H1. *)

assert ( HInd1Simpl :=  HInd1 H1 ).
simpl in *.
clear HInd1.
assert ( HInd2 := IHstmtM2
                              st2j 
                              state1 
                              stateF
                              stateAux
                              (fun s => 
                                 p_and (p_eq (neval state1 stateAux n) 0) (Pre (state1, stateAux) ) ) 
                              assF
                              ).

 rewrite
 ( applicationToConstFuncts ( p_and (p_eq (neval state1 stateAux n) 0) (Pre (state1, stateAux)) ) state1 ) in  HInd2.
(* rewrite <- (progExprEvalProp1 stateAux) in H10. *)
assert ( HInd2Simpl :=  HInd2 H10 ).
simpl in *.
clear HInd2.
assert (thiersExclu := classic  ((neval state1 stateAux n) = 0 ) ).
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
split .
split.
destruct H14.
assumption.
assumption.
destruct H14.
assumption.
(* assert (invAtEndOfIter := relationBtwStates inv state1 stateAux lVar z H11).
simpl in *.
unfold stateAtLoop.
apply (invAtEndOfIter  stateAux0).
exists state1.
split.
trivial.
apply  H13.
assumption.
assumption.
assumption. 
*)

(* sequence *)
inversion HStrongestPost; subst ...
assert ( HIndSt1 := IHstmtM1   st1j state1 state0  stateAux Pre ass1  H1 ).
assert ( HIndSt2 := IHstmtM2   st2j state0 state2 stateAux  (fun _ => ass1) SP   H9 ).
 rewrite
 ( applicationToConstFuncts ass1 state0  ) in  HIndSt2.
apply HIndSt2.
apply HIndSt1.
assumption.
Qed.




(*RELATION WP AND SP *)
(* ( P -> WP(ST, Q) ) -> (Q -> SP (ST, P)) *)
Axiom relWpSp : forall stmtM stmtJ WP Pre Post SP  statePre statePost stateAux ,
( is_wpMod  stmtM Post  WP ) ->
                    ( (evalMyProp ( Pre  (statePre, stateAux ))) -> ( evalMyProp ( WP  (statePre, stateAux ))) ) ->
 (sp  ( (Pre (statePre, stateAux)) , statePre , stateAux, stmtM   ) (  stmtJ, SP ,  statePost, stateAux  )) ->    
((evalMyProp SP ) ->  (evalMyProp  (Post (statePost, stateAux ) ) )).


Inductive wpAssume  :   stmtJAssume -> Assertion -> Assertion -> list Assertion -> Prop:=
| wpSkipAss : forall post z,    ( wpAssume   (SkipAssume z) post  post nil )
| wpSeqAss : forall s1 s2 post p2 P2 p1 P1 z, 
                    ( wpAssume s2 post p2  P2) -> 
                    ( wpAssume s1  p2 p1  P1) ->
                    (wpAssume (SeqAssume z  s1 s2) post p1  (P1 ++ P2 ) )
| wpAffectAss: forall post v exp z , 
                    ( wpAssume 
                      (AffectAssume z v exp)  
                      post   
                      (fun s => let (st, stAux ) := s in
                                             post ((update st v (neval st stAux exp)), stAux ) )  nil)
| wpIfAss: forall pT PT pF PF post cond thenSt elseSt z, 
                    ( wpAssume thenSt post pT PT) -> 
                    ( wpAssume elseSt post pF PF) ->
                    (wpAssume (IfAssume z  cond thenSt elseSt )  
                                         post 
                                         ((fun s =>   let (st, stAux ) := s in 
                                                              p_and ( p_implies (p_neq (neval st stAux  cond) 0) (pT s) ) 
                                                                         ( p_implies (p_eq   (neval st stAux cond)  0) (pF s))) )
                                         (PT ++ PF ) )

(*TODO ; apply the substitutions from listModSubst on  Cs Ci Pl *)
| wpWhileAss : forall stmt inv pI PI cond  substState (post  : Assertion) z,
                 ( wpAssume stmt inv pI PI) -> 
                 let Cs := fun s : State * AuxState =>  let (st, stAux ) := s in 
                                                 (p_implies (p_and  (inv (substState, stAux) )  (p_neq (neval substState stAux cond) 0))  (pI (substState, stAux)) )  in
                 let Ci := fun s : State * AuxState =>  let (st, stAux ) := s in
                                                 (p_implies (p_and (inv (substState, stAux) ) (p_eq (neval substState stAux cond)  0)) (post  (substState, stAux)) ) in
                ( wpAssume (WhileAssume z  (inv_j inv)  substState cond stmt )  post inv  ( Cs :: Ci ::  PI ) ).

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

Lemma spStrongerThanPre : forall stmtm  stmtj Pre Post statePre statePost stateAux , 
  (sp (Pre , statePre , stateAux , stmtm) ( stmtj , Post , statePost, stateAux  )) -> 
  ( (evalMyProp Post )->  
  (evalMyProp Pre ) ).
 Proof with auto.
 intros stmtM; induction stmtM; intros until stateAux; intros Hsp Hpost.
inversion Hsp; subst...
inversion Hsp; subst...
inversion Hsp; subst...
simpl in Hpost.
destruct Hpost.
assert(Hfalse := (IHstmtM2  _ _ _ _ _  stateAux H10 H)).
simpl in Hfalse; destruct Hfalse...
assert(Htrue := (IHstmtM1 _ _ _ _ _  stateAux H1 H)).
simpl in Htrue; destruct Htrue...

(* while *)
inversion Hsp. 
(* unfold stateWithMod in H1, H7, H8, H10, H11, H; *)
(*commented because of the change in the sp def - add a check that z is fresh . clear stateWithMod; *) 
unfold newInv in *.
subst...
assert(Hs := (IHstmtM _ _ _ _ _ _ H15  ))... (* originally the hypothesis was H11 . The proof Changed because  of the change in the sp def *)
simpl in Hpost.
simpl in Hs.
destruct Hpost as [[Hpost1 Hpost2] Hpost3]...

(* seq *)
inversion Hsp; subst...
assert(Hs1 := (IHstmtM1 _ _ _ _ _ stateAux H1 )).
assert(Hs2 := (IHstmtM2 _ _ _ _ _ stateAux H9 ))...
Qed.
 



(* wpMod  is monotone *)
Lemma  wpModMon : forall stmtM  Post1 Post2 Pre1 Pre2 ,
(is_wpMod stmtM Post1 Pre1) ->  
(is_wpMod stmtM Post2 Pre2) -> 
 ( forall (st : State) (stAux : AuxState) , (evalMyProp (Post1 (st, stAux) ) ) -> (evalMyProp (Post2 (st, stAux) )) )   ->  
(forall  (st : State) (stAux : AuxState), ( (evalMyProp (Pre1  (st, stAux)) ) -> (evalMyProp (Pre2 (st, stAux) ))) )   .

Proof with auto.
intro stmtM. induction stmtM; intros until Pre2; intro wpMod1; intro wpMod2.
(*skip*)
inversion wpMod1; subst...
inversion wpMod2; subst...

(*assign*)
intros.
inversion wpMod1; subst...
inversion wpMod2; subst...
assert ( instantiateH := H ( update st  v (neval st stAux n) ) ).
unfold update_assert in *.
assert ( hypIdenticToGoal := instantiateH stAux H0).
exact hypIdenticToGoal.

(*if *)
intros.
inversion wpMod1; subst...
inversion wpMod2; subst...
assert (hypIndThen := IHstmtM1 Post1 Post2   pre_t  pre_t0 H8 H10 ).
assert (hypIndElse := IHstmtM2 Post1 Post2   pre_f  pre_f0 H7 H9 ).
simpl...
simpl in *.
split.
intros.
assert (hypThen := hypIndThen H ).
destruct H0.
assert ( trueCase := H0 H1 ).
assert ( hypThen1 := hypThen st stAux trueCase ).
exact hypThen1.

intros.
assert (hypElse := hypIndElse H).
destruct H0.
assert (falseCase := H2 H1 ).
assert (hypElse1 := hypElse st stAux falseCase).
exact hypElse1.



(*While*)
intros  Post1_impl_Post2.
inversion wpMod1; subst...
inversion wpMod2; subst...
simpl in *.
split.

destruct  H as [ inv [varNotMod quantOverAux]] .
exact inv.
split.
destruct  H as [ inv [varNotMod quantOverAux]] . 
assert ( invPreser_loopTerm := quantOverAux stAux).

destruct invPreser_loopTerm as [ inv_Preserv   inv_Impl_Post ].  
unfold FreezeVarAtIterStart in *.
assert  (  NotModIH := IHstmtM _ _  _ _ H8 H14).
simpl in *.
assert ( triv : (forall (st : State) (stAux : AuxState),
            (forall var : Var,
             ~ In var lVar -> stAux (AuxName var z) = st var) ->
            forall var : Var, ~ In var lVar -> stAux (AuxName var z) = st var)   ). 
intros st0 stAux0.
auto.
apply ( NotModIH triv).
assumption.
split.
(* loop preservation case  *)
intros.
destruct  H as [ inv [varNotMod quantOverAux]] . 
assert ( invPreser_loopTerm := quantOverAux stAux0).
destruct invPreser_loopTerm as [ inv_Preserv   inv_Impl_Post ].  
 assert ( inv_Impl_Post1 := inv_Preserv st0  H0 ).
assert  (  LoopPreservCase := IHstmtM _ _  _ _ H9 H15).
assert ( triv :   (forall (st : State) (stAux : AuxState),
            evalMyProp (invariant (st, stAux)) ->
            evalMyProp (invariant (st, stAux)))).
intros st1 stAux1.
auto.
apply ( LoopPreservCase  triv   ( stateAtLoop st0 stAux0 z lVar  )  stAux0 ). 
assumption.

(*loop termination case *)
intros.
destruct  H as [ inv [varNotMod quantOverAux]] . 
assert ( invPreser_loopTerm := quantOverAux stAux0).
destruct invPreser_loopTerm as [ inv_Preserv   inv_Impl_Post ].  
 assert ( inv_Impl_Post1 := inv_Impl_Post st0  H0 ).
apply ( Post1_impl_Post2 ( stateAtLoop st0 stAux0 z lVar )  stAux0). 
assumption.


(*Sequence *)
intros.
inversion wpMod1; subst...
inversion wpMod2; subst...
assert ( hypInd2 := IHstmtM2 Post1 Post2 pre_st2 pre_st0 H6 H8 H).
assert ( hypInd1 := IHstmtM1 pre_st2 pre_st0 Pre1 Pre2 H7 H9 hypInd2).
assert (hypIdentGoal := hypInd1 st stAux H0).
exact hypIdentGoal.
Qed.

(**************************  wpMod represents a total function relation *********************************************************************)
Axiom wpModTotal : forall stmtM Post, exists Pre,  (is_wpMod stmtM Post Pre).
Axiom etaExpansion: forall s: State, s = (fun v : Var => s v).


Lemma Pre_implies_wp_of_sp : forall stmtM stmtJ ( PRE : myProp ) 
sPost statePre statePost auxState wPre , 
  ( sp ( PRE   , statePre , auxState, stmtM) ( stmtJ,  sPost , statePost,  auxState  ) )->  
  ( is_wpMod  stmtM ( fun s =>  sPost)  wPre ) -> 
  (   (evalMyProp  PRE  ) -> ( evalMyProp ( wPre  (statePre , auxState ) ) )  ) .

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

assert ( IHypThen1 :=  (IHstmtM1 st1j (   p_and (p_neq (neval statePre auxState n) 0) PRE )   assT  statePre stateT auxState wpExists  H2 wpAssT)).
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
assert ( wpExistsHoldsInState0 :=  IHypThen1   (conj cond H)  ).
(* assumption. *)
simpl in *.
apply (applyMonotThenInStatePre statePre  auxState ).
assumption.

(*else case *)
assert ( existsWpElse := wpModTotal  stmtM2 (fun s  => assF)  ).
elim existsWpElse. 
intro wpExists. 
intro wpAssF.
assert ( IHypElse1 :=  (IHstmtM2   st2j (  p_and (p_eq (neval statePre auxState n) 0)   PRE  )   assF  statePre stateF auxState  wpExists H11 wpAssF  )).
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
assert ( wpExistsHoldsInState0 :=  IHypElse1   (conj notCond H)  ).
(* assumption. *)
simpl in *.
apply (applyMonotElseInStatePre statePre  auxState ).
assumption.


(*while *)
inversion WP; subst ...
inversion SP; subst ... 


simpl in *.
split.
apply H19.
assumption.
split.
Focus 2.
intro stAux.
split.
Focus 2.
intros.
split.
split.
destruct H20.
assumption.
assumption.
destruct H20.
assumption.
Focus 2.
assert ( existsWPfor_inv_c_Pre := wpModTotal stmtM ( fun _ =>assIter)  ).
elim  existsWPfor_inv_c_Pre .
intro wp_for_inv_c_Pre.
intro wpRel_for_inv_c_Pre.
clear existsWPfor_inv_c_Pre. 
assert ( HI1 :=   IHstmtM 
                           stmtj 
                           ( p_and
                                   (p_and PRE
                                         (invariant (stateAtLoop stateIterStart auxState z lVar, auxState)))
                                   (p_not
                                         (p_eq (neval (stateAtLoop stateIterStart auxState z lVar) auxState n) 0)))
                           assIter 
                           ( stateAtLoop stateIterStart auxState z lVar) 
                           stateIter 
                           auxState
                           wp_for_inv_c_Pre  
                           H21
                           wpRel_for_inv_c_Pre).
simpl in *.
assert ( relBtwPost := spStrongerThanPre 
                                       stmtM 
                                       stmtj 
                                       ( p_and
                                              (p_and PRE
                                                    (invariant (stateAtLoop stateIterStart auxState z lVar, auxState)))
                                       (p_not (p_eq (neval (stateAtLoop stateIterStart auxState z lVar) auxState n) 0)))  
                                       assIter 
                                       ( stateAtLoop stateIterStart auxState z lVar) 
                                       stateIter 
                                       auxState
                                       H21
                                       ).
simpl in *.
intros.
assert ( assIter_implies_invAtStateLoop:  
forall (state : State) ( stateAux: AuxState) , 
evalMyProp assIter ->
 evalMyProp (invariant (stateAtLoop stateIterStart auxState z lVar, auxState))) .
intros state stateAux assIter1 .
assert  ( inv_in_conj := relBtwPost assIter1 ).
destruct inv_in_conj .
destruct H1.
assumption.
monot
(*seq*)
Qed. 
Lemma spStrongerThanPre : forall stmtm  stmtj Pre Post statePre statePost stateAux , 
  (sp (Pre , statePre , stateAux , stmtm) ( stmtj , Post , statePost, stateAux  )) -> 
  ( (evalMyProp Post )->  
  (evalMyProp Pre ) ).

(* the axiom (which must be  a lemma ) says that  sp returns closed formulas *)
 (* Axiom spClosed :  forall stmtm stmtj Pre Post zPre zPost statePre statePost ,
(sp ( Pre , statePre , zPre , stmtm ) ( stmtj , Post , statePost, zPost ))  -> 
forall state , ( fun s : State => Post ) state = Post .  *)


	   






(**************************  wpMod represents a total function relation *********************************************************************)


Axiom TRich : False.

(* Lemma Pre_implies_wp_of_sp : forall stmtM stmtJ PRE  sPost  zPre zPost statePre statePost wPre , 
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
apply (IHstmtM2 st2j  ( fun  st => st = ass1) sPost z1 zPost st statePost pre_st2 ).



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




*)


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
 Lemma wpModImplieswp : forall stmtM  P Q preM preJ listPogJ  stmtJ (assPost : myProp)  statePre  stateSP stateAux  ,
                    ( is_wpMod  stmtM Q  preM ) ->
                    ( (evalMyProp ( P  (statePre , stateAux) )) -> ( evalMyProp ( preM  (statePre, stateAux))) ) ->
                   (sp  ( (P (statePre , stateAux) ) , statePre, stateAux,  stmtM   ) (  stmtJ, assPost ,  stateSP, stateAux   ) ) ->  
                   (wpAssume stmtJ Q  preJ listPogJ )  -> 
                                  ((evalMyProp ( P (statePre , stateAux) )  -> ( evalMyProp ( preJ (statePre, stateAux) )) )  /\ 
                                         (forall s sAux,  (forall f: Assertion, (In f listPogJ) -> ( evalMyProp (f (s, sAux) )   )))).
Proof with  auto.


intro stmtM.
induction stmtM; intros until stateAux ; intros HwpMod Himply Hsp  HwpAssume. 


(* skip *)
inversion HwpMod; subst...
inversion Hsp; subst ...
inversion HwpAssume; subst ...
split.
assumption.
intros s sAux f absurde;
inversion absurde.

(* affect *)
inversion HwpMod; subst...
inversion Hsp; subst ...
inversion HwpAssume; subst ...
split.
unfold update_assert.
unfold update_assert in Himply.
assumption.
intros s sAux f absurde;
inversion absurde.


(* If *)

inversion HwpMod; subst...
inversion Hsp; subst ...
inversion HwpAssume; subst ...

 assert (hypPandCimplPreT :  ( evalMyProp ((fun s : State*AuxState => 
 let (st, stAux ) := s in   
 p_and (p_neq (neval statePre stateAux n) 0) (P (st , stAux)) ) (statePre , stateAux) ) ) -> 
 ( evalMyProp ( pre_t ( statePre, stateAux) ) )  ).
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
simpl in *.
 assert ( redB :   
    evalMyProp 
   (  ( fun st : State*AuxState =>
          let (s, sAux):= st in 
          p_and (p_neq ( neval s sAux n )  0)  (P (s, sAux) ) )
   ( statePre , stateAux ) ) = 
   ( (neval statePre stateAux n) <> 0 /\
                   evalMyProp (P (statePre, stateAux)) )
 ) . 
simpl in *.
auto.
assert ( BLA :  
evalMyProp 
   (  ( fun st : State*AuxState =>
          let (s, sAux):= st in 
          p_and (p_neq ( neval s sAux n )  0)  (P (s, sAux) ) )
   ( statePre , stateAux ) )  ->  evalMyProp (pre_t (statePre, stateAux)) ).

rewrite  redB . 
assumption.
assert ( HypIndThen := IHstmtM1  _ Q pre_t pT PT st1j  assT statePre   stateT stateAux H6 BLA  (*hypPandCimplPreT*) H1  H9 ) .
simpl in *.

assert (hypPandNotCimplPreF :  ( evalMyProp 
(
 ( fun st : State * AuxState => 
          let ( s, sAux):= st in
           p_and
             (p_eq (neval statePre stateAux n) 0) 
             (P (s, sAux) ) ) (statePre, stateAux))  -> 
( evalMyProp ( pre_f ( statePre, stateAux) ) )
)).

(* debut preuve assert *)
simpl.
intros [Hf Hp].
simpl in Himply.
assert ( h := Himply Hp ).
destruct h as [Hpre_t Hpre_f].
exact (Hpre_f Hf).
(* fin preuve assert *)

assert ( HypIndElse := (IHstmtM2  (*(fun s : State => p_and (p_eq (neval statePre n) 0) (P s) )*)  _ Q pre_f pF PF st2j  assF statePre stateF stateAux H5 hypPandNotCimplPreF H12 H10 )) .
simpl in HypIndThen .
simpl in HypIndElse.
destruct HypIndThen as [HThenPre HThenVc].
destruct HypIndElse as [HElsePre HElseVc].
split.
(* *************** preuve des pres ******************* *)
(* proof of the truth case *)
intro.
simpl in *.
split. 
intros.
apply HThenPre.
split.
assumption.
assumption.

(* proof of the false case *)
intros.
apply HElsePre.
split.
assumption.
assumption.
(* fin preuve pres *)

(* preuve vcs *)
intros s sAux f h.
assert(h1 :=  in_app_or _ _ _ h).
destruct h1...
(*fin preuve vcs *)


(*While *)
inversion HwpMod; subst...
inversion HwpAssume ; subst ...
inversion Hsp. 
unfold lVar0.
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