Require Import semantiqueAux. 
Require Import Ensembles.
Require Import List.
(* Require Import wp. *)
Require Import wpModAux.
Require Import ZArith.
Require Import Classical.

(* language *)
Inductive  stmtJAssume : Set := 
 | SkipAssume : Z -> stmtJAssume
 |  AffectAssume : Z -> Var -> NumExpr -> stmtJAssume
(* | Assume  : State -> Assertion -> stmtJAssume*)
 | SeqAssume : Z -> stmtJAssume -> stmtJAssume -> stmtJAssume 
 | IfAssume : Z  (*->  ( State * AuxState)  *) -> NumExpr -> stmtJAssume  ->  stmtJAssume  -> stmtJAssume  
(*note that the second argument is a list of pairs of prog variables and auxiliary variables, but we do not see the difference as both variables are from the type Var *)
 | WhileAssume : Z -> Invariant_j -> ( State * AuxState) -> NumExpr ->  stmtJAssume  ->  stmtJAssume  .

(* TODO implemenyta function *)
Inductive isStmtInd : stmtJAssume   -> Z -> Prop :=
 | skipInd : forall z , (isStmtInd (SkipAssume z) z)
 | affectInd : forall z  var exp  ,     (isStmtInd (AffectAssume z var exp) z)
 | seqInd : forall z st1 st2  ,  (isStmtInd (SeqAssume z st1 st2 ) z)
 | ifInd : forall z cond  (* state auxState *) st1 st2, (isStmtInd ( IfAssume z (* (state , auxState) *)  cond st1 st2 ) z)
 | whileInd : forall z inv state auxState cond stmt, 
         (isStmtInd (WhileAssume z inv (state , auxState)  cond stmt ) z)
.

(* TODO *)
Axiom stmtIndUnique : forall z1 z2 stmt, 
( isStmtInd stmt z1  )  -> ( isStmtInd stmt z2  )  -> z1 = z2.

(*operational semantics *)
Inductive execStmtAss  : State -> stmtJAssume    -> State -> Set :=
| execSkipAss : forall s z, execStmtAss s (SkipAssume z) s
| execAffectAss : forall s v exp sAux z ,   
            execStmtAss s (AffectAssume  z v exp) (update s v (neval s sAux exp))
| exectBsIfTrue: forall s s' cond  stThen stElse sAux z, 
           neval s sAux cond <> 0 -> 
           execStmtAss s stThen s'  ->
           execStmtAss s (IfAssume z  cond stThen stElse) s'
| exectBsIfFalse: forall s s'  cond stThen stElse sAux z , 
           neval s sAux cond = 0 -> 
           execStmtAss s stElse s'  ->
           execStmtAss s (IfAssume z  cond stThen stElse) s'
| execBsWhileFalse: forall inv substState  cond  stmt  s sAux z , neval s sAux cond = 0 -> 
          execStmtAss s (WhileAssume z (inv_j inv)  substState  cond  stmt) s
| execBsWhileTrue: forall inv   substState cond stmt   s s' s'' sAux z, 
          neval s sAux cond <> 0 -> 
          (execStmtAss s stmt s') -> 
          (execStmtAss s' (WhileAssume  z (inv_j inv) substState  cond   stmt) s'') ->
          (execStmtAss s  (WhileAssume  z (inv_j inv) substState  cond   stmt) s'') 
| execBsSeq: forall s s' s'' st1 st2 z, 
          execStmtAss s st1 s' ->
          execStmtAss s' st2 s'' -> 
          execStmtAss s (SeqAssume z st1 st2) s''.


(*operational semantics *)
Inductive execStmtAux  : AuxState ->  State -> stmtJAssume    -> State -> Set :=
| execSkipAux : forall auxState s z, 
            ( forall var ,   ( auxState (AuxName var ( z )) ) =   ( auxState (AuxName var ( z + 1)) ) )   ->
            ( forall var ,   ( auxState (AuxName var ( z )) ) =  (s var ) )   ->
            ( execStmtAux auxState s  (SkipAssume z) s )
| execAffectAux : forall auxState s v exp sAux z ,   
            ( auxState (AuxName v z) ) = ( s v )   ->
            ( auxState (AuxName v ( z + 1 )) ) = ( neval s sAux exp)   ->
            ( forall var , var  <> v     ->  ( auxState (AuxName var ( z )) ) =  (s var ) ) ->
            ( forall var , var  <> v     ->  ( auxState (AuxName var ( z + 1 ))  = ( (update s v (neval s sAux exp) ) var ))) ->
            execStmtAux auxState s (AffectAssume  z v exp) (update s v (neval s sAux exp) )
| exectBsIfTrueAux: forall auxState s s' cond  stThen stElse sAux z zThen , 
           neval s sAux cond <> 0 -> 
           execStmtAux auxState  s stThen s'  ->
           (isStmtInd (IfAssume z cond stThen stElse)  z) ->
           (isStmtInd stThen zThen) ->
            ( forall var ,   ( auxState (AuxName var ( zThen )) ) =   ( auxState (AuxName var ( z)) ) )   ->
            ( forall var ,   ( auxState (AuxName var ( zThen )) ) =  (s var ) )   ->
           execStmtAux auxState s (IfAssume z   cond stThen stElse) s'
| exectBsIfFalseAux: forall auxState s s'  cond stThen stElse sAux zElse z , 
           neval s sAux cond = 0 -> 
           execStmtAux auxState  s stElse s'  ->
            (isStmtInd (IfAssume z cond stThen stElse)  z) ->
           (isStmtInd stElse zElse) ->
           ( forall var ,   ( auxState (AuxName var ( zElse )) ) =   ( auxState (AuxName var ( z)) ) )   ->
           ( forall var ,   ( auxState (AuxName var ( zElse )) ) =  (s var ) )   ->
           execStmtAux auxState s (IfAssume z  cond stThen stElse) s'
| execBsWhileFalseAux: forall auxState  inv substState  cond  stmt  s   z , 
          neval s auxState  cond = 0 -> 
            (isStmtInd (WhileAssume z (inv_j inv)  substState  cond  stmt)  z) ->
        (*   ( forall var ,   ( auxState (AuxName var ( zB )) ) =   ( auxState (AuxName var ( z)) ) )   -> *)
           ( forall var ,   ( auxState (AuxName var ( z )) ) =  (s var ) )   ->
          execStmtAux  auxState s (WhileAssume z (inv_j inv)  substState  cond  stmt) s
| execBsWhileTrueAux: forall auxState  inv   substState cond stmt   s s' s'' sAux zB z, 
          neval s sAux cond <> 0 -> 
              (isStmtInd (WhileAssume z (inv_j inv)  substState  cond  stmt)  z) ->
          (execStmtAux auxState  s stmt s') -> 
          (  isStmtInd  stmt zB) -> 
         (*  ( forall var ,   ( auxState (AuxName var ( zB )) ) =   ( auxState (AuxName var ( z)) ) )  *)  
        (*  ( forall var ,   ( auxState (AuxName var ( zB )) ) =  (s var ) )   -> *)
          (execStmtAux auxState s' (WhileAssume  z (inv_j inv) substState  cond   stmt) s'') ->
          (execStmtAux auxState s  (WhileAssume  z (inv_j inv) substState  cond   stmt) s'') 
| execBsSeqAux: forall auxState s s' s'' st1 st2 z1 z, 
          execStmtAux auxState  s st1 s' ->
          execStmtAux auxState  s' st2 s'' -> 
           (isStmtInd st1 z1) -> 
          ( forall var ,   ( auxState (AuxName var ( z1 )) ) =   ( auxState (AuxName var ( z)) ) )   ->
           ( forall var ,   ( auxState (AuxName var ( z1 )) ) =  (s var ) )   ->
          execStmtAux auxState s (SeqAssume z st1 st2) s''.

Inductive  pogSubst :   list Assertion ->  State -> AuxState -> list Assertion  -> Set :=
 |empty : forall pogs state auxState , pogs = nil -> ( pogSubst pogs state auxState pogs) 
 | notEmpy : forall ( head : Assertion) tail state auxState  headS tailS  , 
                      headS  =  (fun _ => head ( state, auxState) )  -> 
                      ( pogSubst tail state auxState tailS) ->
                      ( pogSubst  (head :: tail)  state auxState ( headS :: tailS ) ).


 
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
| wpIfAss: forall pT PT pF PF  post cond thenSt elseSt     z, 
                    ( wpAssume thenSt post pT PT) -> 
                    ( wpAssume elseSt post pF PF) ->
                    (wpAssume (IfAssume z  cond thenSt elseSt )  
                                         post 
                                         ((fun s => let (state, stateAux) := s in
                                            p_and ( p_implies (p_neq (neval state  stateAux cond) 0) ( pT  ( state , stateAux)) ) 
                                                       ( p_implies (p_eq   (neval state stateAux cond)  0) (pF    ( state , stateAux)))) )
                                         (PT ++ PF ) )

(*TODO ; apply the substitutions from listModSubst on  Cs Ci Pl *)
| wpWhileAss : forall stmt inv pI PL cond  substState substStateAux (post  : Assertion)  PLS z,
                 ( wpAssume stmt inv pI PL) -> 
                 let Cs := fun _ : State * AuxState =>  (* let (st, stAux ) := s in *)
                                                 (p_implies (p_and  (inv (substState, substStateAux ) )  
                                                                                   (p_neq (neval substState substStateAux cond) 0))  
                                                                    (pI (substState, substStateAux )) )  in
                 let Ci := fun _ : State * AuxState =>  (* let (st, stAux ) := s in *)
                                                 (p_implies (p_and (inv (substState, substStateAux) ) 
                                                                                  (p_eq (neval substState substStateAux cond)  0)) 
                                                                    (post  (substState, substStateAux )) ) in
                 (pogSubst PL substState substStateAux PLS ) ->
                ( wpAssume (WhileAssume z  (inv_j inv)  (substState, substStateAux) cond stmt )  post inv  ( Cs :: Ci ::  PLS ) ).






(* 
Axiom FALSE : False.
Lemma wpAssumeCorrect : 
forall (stateAux : AuxState  ) ( state1: State) (stmt : stmtJAssume ) (state2: State) z ,
       ( execStmtAux  stateAux state1 stmt  state2) -> 
       forall (pre post : Assertion) VCList ,   ( wpAssume stmt  post  pre VCList )  ->
       (isStmtInd stmt z) ->
       ( forall   state  , ( forall v , (stateAux (AuxName v z ) ) = (state v ) ) ->   
       forall vc,  ( In  vc VCList ) -> ( evalMyProp ( vc (state, stateAux) ) )   ) ->
      (   (evalMyProp ( pre (state1,  stateAux))) -> ( evalMyProp (post (state2 , stateAux)) )).
Proof with auto.
intros stateAux state1 stmt state2 z Hexec; induction Hexec;
intros pre post VClist Hwp index ;
 auto...

(* skip *) 

inversion Hwp. subst.  intros. simpl in *.
 auto...
(* assign *)

(* pre holds *)
inversion Hwp. subst.  intros. simpl in *.
rewrite <- (progExprEvalProp1 auxState).
assumption.

(*if *)
(*then case *)
inversion Hwp. subst.  intros. simpl in *.
rewrite <- (progExprEvalProp1 auxState) in n.
 assert ( IHthen1 := IHHexec _ _ _ H7 ). 
destruct H0 as [ varEqAuxVar conditions] .
apply IHthen1.
Focus 2.


assert ( ZeqZ0 : z = z0).
apply (stmtIndUnique z z0   (IfAssume z0 (substState0, substStateAux) cond stThen stElse)  index i).


(*vclist then case *)
assert (reflex :  pogSubst (PT ++PF) z = pogSubst (PT++PF)  z ).
trivial.
(* get the equality bytw aux var and the evaluation of a program variable *)



rewrite <-   ZeqZ0 in varEqAuxVar . 
rewrite <-   ZeqZ0 in H .
intros.
assert (H100 := H state  H0).
assert (listVC1 :=  auxLemma  (PT++PF)  ( pogSubst (PT++PF)  z)  z  state auxState   reflex  H0 H100  ).
apply listVC1.
assert ( disj :=  in_or_app PT PF vc  ).
apply disj.
left .
assumption.
(*TODO - some more info about indexes *)
Focus 2.
destruct (conditions varEqAuxVar  ) as [ thenCase elseCase ].
apply thenCase.
assumption.


(*else  case *)
Focus 2.
inversion Hwp. subst.  intros. simpl in *.

rewrite <- (progExprEvalProp1 auxState) in e.
 assert ( IHthen1 := IHHexec _ _ _ H8 ). 
destruct H0 as [ varEqAuxVar conditions] .
apply IHthen1.
Focus 2.


assert ( ZeqZ0 : z = z0).
apply (stmtIndUnique z z0   (IfAssume z0 (substState0, substStateAux) cond stThen stElse)  index i).


(*vclist then case *)
assert (reflex :  pogSubst (PT ++PF) z = pogSubst (PT++PF)  z ).
trivial.
(* get the equality bytw aux var and the evaluation of a program variable *)



rewrite <-   ZeqZ0 in varEqAuxVar . 
rewrite <-   ZeqZ0 in H .
intros.
assert (H100 := H state  H0).
assert (listVC1 :=  auxLemma  (PT++PF)  ( pogSubst (PT++PF)  z)  z  state auxState   reflex  H0 H100  ).
apply listVC1.
assert ( disj :=  in_or_app PT PF vc  ).
apply disj.
right .
assumption.
(*TODO - some more info about indexes *)
Focus 3.
destruct (conditions varEqAuxVar  ) as [ thenCase elseCase ].
apply elseCase.
assumption.


(*while case *)
 (* false case *)
Focus 3.
intros.
inversion Hwp.
subst.  intros. 
unfold Cs, Ci in *; clear Cs Ci; subst. simpl in *.
 assert ( ZeqZ0 : z = z0). 
apply (stmtIndUnique z z0    (WhileAssume z0 (inv_j pre) (substState0, substStateAux) cond stmt)   index i). 
rewrite  <-  ZeqZ0 in e0. 
assert(h :=  H s  e0 
  (fun s : State * AuxState =>
     let (st, stAux) := s in
     p_and (p_forallv (fun v : Var => p_eq (st v) (stAux (AuxName v z0))))
       (p_implies
          (p_forallv (fun v : Var => p_eq (st v) (stAux (AuxName v z0))))
          (p_implies (p_and (pre (st, stAux)) (p_eq (neval st stAux cond) 0))
             (post (st, stAux)))))).

assert(
    presque : 

evalMyProp  (  (fun s : State * AuxState =>
     let (st, stAux) := s in
     p_and (p_forallv (fun v : Var => p_eq (st v) (stAux (AuxName v z0))))
       (p_implies
          (p_forallv (fun v : Var => p_eq (st v) (stAux (AuxName v z0))))
          (p_implies (p_and (pre (st, stAux)) (p_eq (neval st stAux cond) 0))
             (post (st, stAux)))))

  ( s, auxState) )
       ).
simpl in *.
apply h; intuition.
simpl in *.
destruct presque as [varEqAuxVar conditions].
apply conditions  .
assumption.
intuition.


(*true case *) 
Focus 3.
intros.
inversion Hwp;
unfold Cs, Ci in *; clear Cs Ci; subst.
 assert ( ZeqZ0 : z = z0). 
apply (stmtIndUnique z z0    (WhileAssume z0 (inv_j pre) (substState0, substStateAux) cond stmt)   index i). 

apply (IHHexec2 _ _ _ Hwp index H)...

apply (IHHexec1 _ _ _ H9)...
Focus 2.
intros.
assert (reflex :  pogSubst (PL ) z = pogSubst (PL )  z ).
trivial.
assert (H100 := H state  H1  ).
rewrite <- ZeqZ0 in H100. 
unfold Assertion in H100.
assert (vc_PL: 
 forall vc : State * AuxState -> myProp,
 In vc PL ->  evalMyProp (vc (state, auxState))).
intros.
apply auxLemma with (vcListOneHypMore:=pogSubst PL z) (z:=z) (vcList:=PL);trivial.
intros.
apply H100.
simpl ;auto.
auto.
Focus 4.
apply H; intuition.

assumption.
(*end proof of the list *)
(* assert(h1:= H3 s); simpl in h1.
apply h1... *)


Qed.
*)