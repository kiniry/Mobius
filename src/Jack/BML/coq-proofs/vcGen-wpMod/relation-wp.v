Require Import semantique. 
Require Import Ensembles.
Require Import List.
Require Import wp.
Require Import wpMod.


Inductive transformMod2NoMod : stmt_m -> stmt_j -> Prop:= 
         | transformSkip : ( transformMod2NoMod ( Skip Invariant_m ) ( Skip Invariant_j ))
         | transformAffect : forall x v, (transformMod2NoMod ( Affect Invariant_m x v  ) ( Affect Invariant_j x v ))
         | transformIf : forall s1 s2 s11 s22 c,  ( transformMod2NoMod s1 s11)  ->
            ( transformMod2NoMod s2  s22) ->    
                ( transformMod2NoMod ( If  Invariant_m c  s1 s2 ) ( If  Invariant_j c s11 s22 ) )
         | transformWhile : forall s1 s11 c inv (l : list Var),  ( transformMod2NoMod s1  s11) -> 
                ( transformMod2NoMod  (   While Invariant_m c  ( inv_m inv l ) s1 )  
                                                            (   While Invariant_j   c  ( inv_j 
                                                                                                  ( fun ( s: State  ) => ( inv s /\ forall  x ,exists v,  ~In x l -> x = v)  ) ) s11 ) )
         | transformSeq : forall s1 s2 s11 s22, ( transformMod2NoMod s1 s11) -> 
           ( transformMod2NoMod s2 s22 )  ->
               ( transformMod2NoMod  ( Seq   Invariant_m s1 s2 ) ( Seq   Invariant_j s11 s22 ) ).



Inductive isSp : stmt_m  -> Assertion -> Assertion -> Prop := 
| isSpSkip : forall pre, ( isSp ( Skip Invariant_m) pre  pre)
| isSpAffect :   forall pre var expr, 
  (  isSp  
     (Affect  Invariant_m var expr) 
     pre 
     ( fun (s : State ) => ( exists  v : Num ,  ( update_assert pre var (nval v) ) s /\  
                                         ( (update s var v) var ) =  ( neval (update s var  v) expr ) )  ))
|isSpIf : forall s1 s2 post1 post2  c pre,
    ( isSp s1 ( fun (s: State ) => pre s /\ ( neval s c ) = 0  )  post1   ) ->
    ( isSp s2 ( fun (s: State ) => pre s /\ ( neval s c ) = 1  )  post2   ) ->
    ( isSp (If  Invariant_m c s1 s2) 
    pre
    ( fun (s: State )  => ( post1 s ) \/  ( post2 s )  ) )
| isSpSeq: forall s1 s2 pre  post1 post2, 
    ( isSp  s1 pre  post1) ->
    ( isSp s2 post1 post2) ->
    ( isSp (Seq Invariant_m s1 s2) pre post2)
 |   isSpWhile : forall st1 c (pre inv :Assertion) lVar (post : Assertion),  (* While Invariant_m c *)
  forall ( Sinit : State) ,
(*la precondition preserve l'invariant *)
  (( pre Sinit) -> ( inv Sinit) ) ->
 (*preservation de l'invariant*)
  ( isSp st1 inv ( fun (s: State) => ( neval s c ) = 1    ->  (( inv  s) /\   ( forall  x: Var,   ~In x  lVar  -> s x  = Sinit x ) )) ) ->
(*la postcondition implique l'invariant*)  
(forall s ,  ( (post s ) /\  ( neval s c ) <> 1     /\ (forall  x: Var,   ~In x  lVar  -> s x  = Sinit x) ) -> inv s ) -> 
   ( isSp ( While  Invariant_m c (inv_m inv lVar )  st1) pre post). (*  ( fun (s: State) =>  inv Sfin /\   ( forall  x: Var,   ~In x  lVar  -> s x  = Sfin x )    ) ). *)
   
 

(* Inductive propagate : stmt_m ->  stmt_m -> Prop := *)




(*  Lemma wpModCorrBS: 
    forall (stPost: State) (stPre : State)(stmtM: stmt_m ) (stmtJ:stmt_j)
	( post2 : Assertion) (post1: Assertion) (pre1: Assertion )
	(pre2: Assertion) (vc:  Ensemble Assertion )
	(inv :Assertion) (l : list Var ) (cond: NumExpr) (st: Stmt Invariant),
	stmtM = ( While   Invariant_m  cond (inv_m inv  l) st)    ->
	stmtJ = ( While cond  ( fun s => (inv s /\ forall  x ,exists v,  ~In x l -> x = v) s ) st)    ->	
	 (post1 stPost -> post2 stPost) 	-> 
 			( wp stmtJ post1 pre1 )	-> 
				( is_wpMod  stmtM post2 pre2 vc  ) ->
					  (* forall state: State  (conj vc ) state  /\*)  ( pre2  stPre) ->
								( pre1 stPre) .

*)

Lemma existElim: forall P: Prop, exists x, P x -> P x.





