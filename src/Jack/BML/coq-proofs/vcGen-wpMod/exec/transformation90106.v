Require Import semantique. 
Require Import Ensembles.
Require Import List.
Require Import wp.
Require Import wpMod.
Require Import ZArith.
Require Import Classical.

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
                            (sp st1  (  ( fun s: State => ( p_and  ( p_neq  ( neval state  expB  )  0 )   (ass s ) ) ), state)   ( assT, stateT , st1j ) ) ->
                            (sp   st2 (  ( fun s: State => ( p_and   ( p_eq ( neval state  expB  )  0 )   (ass s ) ) ), state)   ( assF, stateF , st2j) ) ->                       
                            let stateMerge := ( fun var: Var => 
                                                             if  (  Zeq (neval stateT ( nvar var) )  ( neval stateF (nvar var) )) 
                                                             then   ( neval stateT ( nvar var) )
                                                             else (Constant var )) in
                            let   assumeT :=    ( Assume (fun s: State => p_forallv   (fun x: Var =>  p_eq (neval stateT (nvar x ))   (neval stateMerge (nvar x) )))) in 
                            let   assumeE :=    (Assume  (fun s: State => p_forallv   (fun x: Var =>  p_eq (neval stateF (nvar x) )   (neval stateMerge (nvar x) )))) in   
                            ( sp ( If Invariant_m expB  st1 st2)  ( ass, state )  ( fun s: State => ( p_or ( assF s )  ( assT s ) ), 
                            stateMerge,  ( IfAssume expB (SeqAssume st1j assumeT) (SeqAssume st2j assumeE ) )))
  | isSpwhile : forall  expB stmt ass state inv lVar stmtj assIter stateIter , 
                            let stateWithMod  := ( fun var: Var =>  
                                                                         if  ( In_dec varEqDec var lVar ) 
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

Axiom triche: forall p: Prop, p.
(* where " 'vcGenAssume' ( a , p ) ==> ( b , c ) " := (wpAssume a p b c) . *)
 Axiom wpSpRel : forall pre1  post1  post2 pre2  stmt statePre statePost stmtA, 
                          ( is_wpMod   stmt post1 pre1  ) ->  
                          ( evalMyProp (p_implies (pre2 statePre) ( pre1 statePre))) -> 
                          ( sp stmt (pre2, statePre) (post2, statePost, stmtA)) ->
                          ( evalMyProp (p_implies (post2 statePost)  (post1 statePost ))). 


Axiom wpMono1 :
forall post post', (forall s,  evalMyProp (post s) ->  evalMyProp (post' s)) ->
forall s preJ l, wpAssume s post'  preJ l -> wpAssume s post  preJ l.
Axiom spMono :
forall pre pre' st, ( evalMyProp (pre st) ->  evalMyProp (pre' st)) ->
forall sM sJ post sPost, sp sM (pre, st)  (post, sPost, sJ)  -> sp sM (pre', st)  (post, sPost, sJ).
(*  Axiom absurdAssume : 
forall s1 hyp post p P, wpAssume (Seq s post p P -> (forall f s, In f P  -> (evalMyProp (hyp s) -> False) -> evalMyProp (f s)).
*)

Hint Resolve wpSpRel.

Lemma wpModImplieswp : forall stmtM  pre preSp post  stPre preJ listPOGs stmtJ assPost statePost,
                  evalMyProp preSp -> ( is_wpMod  stmtM post  pre ) ->
                    ( evalMyProp (pre stPre)  ) ->
                    (sp stmtM ( fun s => preSp , stPre  )  ( assPost ,  statePost , stmtJ  ) )  ->  
                 (wpAssume stmtJ post  preJ listPOGs )  -> 
                                  ((evalMyProp preSp  -> ( evalMyProp ( preJ stPre))) /\ 
                                         (forall f: Assertion, (In f listPOGs) -> ( evalMyProp (f stPre)   ))).  
Proof with  auto.
intro stmtM.
induction stmtM; intros until statePost; intros Hpre; intros.


(* skip *)
inversion  H1; subst...
inversion H2; subst...
inversion H; subst...
split...
intros f h; elim h.

(* affect *)
inversion H1; subst...
inversion  H2; subst...
inversion H; subst...
split...
intros f h; elim h.


(* If *)

inversion H1; subst...
inversion H; subst.
inversion H2; subst.

assert(h2 : forall a b c s ass pre,
      (sp s (fun _ : State => p_and ass pre, stPre) (a, b, c))->
      (sp s(fun _ : State => pre, stPre) (a, b, c))).
   (* debut preuve assert *)
    intros.
    eassert(h := (spMono _ (fun _ : State => pre) _ _  s c  _ b H3))...
    simpl... 
   intros [hh hhh]...
   (* fin preuve assert *)
split.
apply triche.
assert (forall f : Assertion, In f (PT) -> evalMyProp (f stPre) /\
forall f : Assertion, In f (PF) -> evalMyProp (f stPre)).
split.
destruct (classic ((neval stPre n) = 0)).
(* if false *)
simpl in H0.
destruct H0.
eassert(h1 := (H4 H3)).
eassert(h3 :=  (h2 _ _ _ _ _ _ H12)).
eassert  (h4 := (IHstmtM2  _ _ _ stPre pF PF _ _ _ _ H9 h1 h3 _))...
(* debut preuve h3 *)
inversion H14; subst.
inversion H8; subst...
 assert (forall s, evalMyProp (post s) -> 
  evalMyProp ((fun s : State =>
         p_implies
           (p_forallv
              (fun x : Var =>
               p_eq (stateF x)
                 (if Zeq (stateT x) (stateF x) then stateT x else Constant x)))
           (post s)) s)).
intros; simpl.
intros...
eassert (h := (wpMono1 _ _ H6  st2j pF (P1 ++ nil) _ ))...
rewrite <- app_nil_end...
(* fin preuve h3 *)


destruct h4.
simpl...
repeat split...
intros h;
destruct h...

assert(h4 : forall f : Assertion, In f PT -> evalMyProp (f stPre)).
(* debut preuve h4 *)
inversion H13; subst...
inversion H15; subst...
(* rewrite <- app_nil_end... *)
intros f hh.

apply (absurdAssume _ _ _ _ _ H13)...
simpl.
intros.
simpl.
induction st1j.
inversion H19; intros f hh; elim hh.
inversion H19; intros f hh; elim hh.
inversion H19; subst.
intros f hh; elim hh.
inversion H19; subst.
apply triche.
(* fin preuve h4 *)



intros f h...
eassert(h' := (in_app_or _ _ _ h)).
destruct h'...

(* if true *)
simpl in H0.
destruct H0.
eassert(h1 := (H0 H3)).

eassert  (h3 := (IHstmtM1 _ _ stPre pT PT _ _ _ H11 h1 (h2 _ _ _ _ _ H5) _)).
inversion H13; subst.
inversion H8; subst...
apply triche.
destruct h3.
simpl...
repeat split...
intros h;
destruct H3...
assert(forall f : Assertion, In f PF -> evalMyProp (f stPre)).
apply triche.
intros f h...
eassert(h' := (in_app_or _ _ _ h)).
destruct h'...


(* while *)
apply triche.

(* seq *)
apply triche.

Qed.