
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


Open Scope Z_scope.

Set Implicit Arguments.




Inductive quadrupleT (A B C D : Type) : Type :=  
 | quadruple : A -> B -> C -> D -> quadrupleT  A B C D .

Unset Implicit Arguments.


Fixpoint translateOptim (pre : assertion ) (st :stmt) ( _state : state){struct st}: quadrupleT stmt  assertion listP state :=
 match st with 
 |  (Affect z x e) =>
    ( quadruple ( Affect z x e)  pre  nilP ( update _state x ( eval_expr _state e) ))
 |  (If z e bT bF) =>
    let preT :=
	fun s => 
	     	pre _state  /\   eval_expr _state e <> 0  in
    let (   btT , SPT  , annexT , stateT) := ( translateOptim  preT bT  _state )  in
    let preF  :=
	fun s =>  
     	pre _state /\ eval_expr  _state e = 0  in

    let (btF , SPF  , annexF , stateF) := ( translateOptim  preF bF _state )   in
    let SP := fun s => SPT s \/ SPF s in
    let annex :=  appendP annexT annexF in
    let stateP := ( fun v : var => 
                       if ( Zeq_bool ( eval_expr _state e ) 0  )
                       then ( stateF v  )  
                       else ( stateT v  ) ) in

   (  quadruple ( If z e btT btF)  SP annex stateP )


 |  (While z e (Inv inv l) body)    =>
    
    let statePre := ( fun v stateAux  =>  if ( In_dec Z_eq_dec  v l )  
                                              then ( stateAux ( aux v z ) ) 
                                              else ( _state v ) )   in 
    let invA  := fun s => 
                        ( inv s /\ 
                        ( forall x, ~In x l -> s x = _state x   ) /\ 
                        ( pre _state ) ) in
    let (bodyT , SPB , annexB, stateBody) :=   
    let preBody  := ( fun s =>                             
                               ( eval_expr  statePre e <> 0 /\ 
                               ( inv s ) /\ 
                               ( forall x, ~In x l -> s x = _state x) /\ 
                               ( pre statePre ) ))  in
    ( translateOptim  preBody  body  statePre )  in
     let SP :=  fun s => 
               
                               ( eval_expr  statePre e =  0 /\ 
                               ( inv s ) /\ 
                               ( forall x, ~In x l -> s x = _state x ) /\ 
                               ( pre statePre ) )   in
     let annex1 :=  pre statePre -> invA statePre in
     let annex2 :=  SPB statePre -> invA statePre in
     let annex := ( consP annex1 (consP annex2 annexB ) ) in 
    ( quadruple (While z e ( Inv invA nil) bodyT )  SP annex  statePre)

 |  Snil z => (quadruple   Snil  pre nilP _state ) 
 
 |  Sseq z st1 st2 =>
    let (stT1, SP1, annex1 , state1 )  :=  translateOptim pre st1 _state     in
    let (stT2, SP2, annex2 , state2 )  :=  translateOptim SP1 st2  state1 in
    let annex := appendP annex1  annex2 in
    ( quadruple  (Sseq stT1 stT2 )  SP2  annex state2 )
 end.
