Require Import semantique. 
Require Import Ensembles.
Require Import List.
Require Import wp.
Require Import wpMod.



 Inductive stmtJAssume : Set := 
 (* | Statement :  Stmt Invariant_j -> stmtJAssume *)
 | SkipAssume : stmtJAssume
 |  AffectAssume : Var -> NumExpr -> stmtJAssume
 | Assume  : Assertion -> stmtJAssume
 | SeqAssume : stmtJAssume -> stmtJAssume -> stmtJAssume 
 | IfAssume : NumExpr -> stmtJAssume  ->  stmtJAssume  -> stmtJAssume  
 | WhileAssume : Invariant_j ->  NumExpr ->  stmtJAssume  ->  stmtJAssume  .

(* a function for generating fresh variables *)
Inductive  fresh : list Var -> Var -> Prop := 
|isFresh : forall lVar y  , ~(In y lVar ) -> (fresh lVar y).
   
(* a function  for generating a fresh constant*)
Axiom Constant : Var -> Num.
Require Import ZArith.

Inductive sp :  stmt_m ->  Assertion * State  -> (  Assertion *  State * stmtJAssume) -> Prop :=
   | isSpSkip : forall state ass, (sp ( Skip Invariant_m) (ass, state ) (ass, state , SkipAssume ))
   | isSpAssign : forall var expr  ass state state1 , 
                            state1 = (update state var ( neval  state expr ) )->
                            (sp ( Affect Invariant_m var expr ) (ass, state)   ( ass,  state1, ( AffectAssume var expr )  ) ) 
   | isSpSeq : forall  st1 st2 ass state ass1 state1 ass2 state2 st1j st2j  , 
                            ( sp   st1 (ass , state ) (ass1,  state1 , st1j) ) ->
                            ( sp   st2 (ass1, state1) ( ass2, state2, st2j) ) -> 
                            ( sp   (Seq Invariant_m st1 st2) (ass, state) (ass2, state2 , ( SeqAssume st1j st2j ) ))
   | isSpIf : forall   expB st1 st2 ass state assT assF  stateT stateF st2j st1j , 
                            (sp st1  (  ( fun s: State => ( p_and  ( p_eq  ( neval state  expB  )  0 )   (ass s ) ) ), state)   ( assT, stateT , st1j ) ) ->
                            (sp   st2 (  ( fun s: State => ( p_and   ( p_eq ( neval state  expB  )  1 )   (ass s ) ) ), state)   ( assF, stateF , st2j) ) ->                       
                            let stateMerge := ( fun var: Var => 
                                                             if  (  Z_eq_dec   (neval stateT ( nvar var) )   ( neval stateF (nvar var) )) 
                                                             then   ( neval stateT ( nvar var) )
                                                             else (Constant var )) in
                            let   assumeT :=    ( Assume (fun s: State => p_forallv   (fun x: Var =>  p_eq (neval stateT (nvar x ))   (neval stateMerge (nvar x) )))) in 
                            let   assumeE :=    (Assume  (fun s: State => p_forallv   (fun x: Var =>  p_eq (neval stateF (nvar x) )   (neval stateMerge (nvar x) )))) in   
                            ( sp ( If Invariant_m expB  st1 st2)  ( ass, state )  ( fun s: State => ( p_or ( assF s )  ( assT s ) ), 
                            stateMerge,  ( IfAssume expB (SeqAssume st1j assumeT) (SeqAssume st2j assumeE ) )))
  | isSpwhile : forall  expB stmt ass state inv lVar stmtj assIter stateIter , 
                            let stateWithMod  := ( fun var: Var =>  
                                                                         if  ( In_dec  varEqDec var lVar ) 
                                                                         then  ( Constant var )   
                                                                         else  (neval state (nvar var) ) )  in
                            let assumeWhile := (Assume ( fun s: State =>
                                                                 ( p_forallv (fun x: Var =>  
                                                                                 ( p_implies  (p_in  x lVar ) ( p_eq ( neval state  ( nvar x) ) 
                                                                                                                      (stateWithMod x) )))))) in
                            let newInv :=  (fun s: State => ( p_and ( 
                                                                                              p_and (inv s )  
                                                                                                          ( p_forallv ( fun v: Var => (p_implies (p_not ( p_in  v lVar))    ( p_eq ( neval state (nvar v ) )  ( neval s (nvar v) )))))) 
                                                                                               ( ass s ) )) in      
                           (sp stmt ( fun s : State =>  (p_and ( newInv stateWithMod )  
                                                                                     (  p_eq ( neval stateWithMod expB )  1) ) , state ) (assIter, stateIter , stmtj ) ) ->
                               ( sp (While  Invariant_m expB ( inv_m  inv lVar )  stmt ) ( ass , state )     
                                                        (  fun s : State =>  (p_and ( newInv stateWithMod )  
                                                                                                     (  p_eq ( neval stateWithMod expB )  0) ),
                                                           stateWithMod, 
                                                           ( SeqAssume  ( WhileAssume (inv_j newInv) expB  (SeqAssume assumeWhile stmtj ) )  assumeWhile  ))).
                                
(* Reserved Notation "'vcGenAssume ' ( a , p )  ==> ( b , c )" (at level 32). *)
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
| wpWhileAss : forall i inv pI PI b (a: Assertion),
                 ( wpAssume i inv pI PI) -> 
                 let Cs := fun s => (p_implies (p_and  (inv s)  (p_neq (neval s b) 0))  (pI s)) in
                 let Ci := fun s => (p_implies (p_and (inv s) (p_eq (neval s b)  0)) (a  s) ) in
                ( wpAssume (WhileAssume  (inv_j inv)  b i)   a inv  ( Cs :: Ci ::  PI ) )
| wpAssumeAss : forall (hyp: Assertion )  post  ,
                ( wpAssume (Assume hyp ) post ( fun s : State => (p_implies (hyp s) )  (post s )  ) nil ) .

(* where " 'vcGenAssume' ( a , p ) ==> ( b , c ) " := (wpAssume a p b c) . *)
 Axiom wpSpRel : forall pre1  post1  post2 pre2  stmt statePre statePost stmtA, 
                          ( is_wpMod   stmt post1 pre1  ) ->  
                          ( evalMyProp (p_implies (pre2 statePre) ( pre1 statePre))) -> 
                          ( sp stmt (pre2, statePre) (post2, statePost, stmtA)) ->
                          ( evalMyProp (p_implies (post2 statePost)  (post1 statePost ))). 
Lemma wpModImplieswp : forall stmtM  pre  post  stPre preJ listPOGs stmtJ assPost statePost,
                 (  ( is_wpMod  stmtM post  pre ) /\  
                    ( evalMyProp (pre stPre)  ) /\ 
                    (sp stmtM ( fun s: State => p_true , stPre  )  ( assPost ,  statePost , stmtJ  ) ) ) ->  
                 (wpAssume stmtJ post  preJ listPOGs )  -> ( ( evalMyProp ( preJ stPre)) /\ 
                                                                                 forall f: Assertion, (In f listPOGs) -> ( evalMyProp (f stPre)   )).  
  intros.
split.
induction stmtM.

destruct H.
destruct H1.
inversion  H2.
inversion H0.
inversion H.
rewrite <- H7.
rewrite <- H10.
rewrite H14.
assumption.