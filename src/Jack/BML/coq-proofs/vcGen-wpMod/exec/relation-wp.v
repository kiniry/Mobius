Require Import semantique. 
Require Import Ensembles.
Require Import List.
Require Import wp.
Require Import wpMod.


Axiom triche: forall p: Prop, p.


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

Reserved Notation "'m2j' s1 ==> s2" (at level 30).

Inductive Stmt_mToStmt_j : Stmt Invariant_m -> Stmt Invariant_j -> Prop :=
| Stmt_m2jSkip : m2j (Skip Invariant_m) ==>  (Skip Invariant_j)
| Stmt_m2jAffect : forall v val, 
                    m2j (Affect Invariant_m v val) ==> (Affect Invariant_j v val)
| Stmt_m2jIf : forall b t t' f f', 
                   m2j t ==> t' -> m2j f ==> f' -> 
                   m2j (If Invariant_m b t f) ==>  (If Invariant_j b t' f')
| Stmt_m2jWhile : forall b  s s' (l: list Var) v pre im pred,
               (wpMod(pred,  fun s : State => (forall  x: Var,   ~In x  l  -> s x  = v)) ==> pre) ->
               m2j s ==> s' -> 
              m2j (While Invariant_m b (inv_m im l) s) ==>  (While Invariant_j b (inv_j (fun state => im state /\ (forall  x: Var,   ~In x  l  -> state x  = v) /\  (pre state))) s')
| Stmt_m2jSeq : forall s1 s1' s2 s2', 
                   m2j s1 ==> s1' -> m2j s2 ==> s2' -> 
                   m2j (Seq Invariant_m s1 s2) ==>  (Seq Invariant_j s1' s2')
where "'m2j' s1 ==> s2" :=   (Stmt_mToStmt_j s1 s2).



Lemma imp1:
forall  Sj post vcPre (Pre : Ensemble Assertion), 
 (vcGen(Sj, post) ==> (vcPre, Pre)) ->
forall Sm, m2j Sm ==> Sj ->
forall pre,    wpMod(Sm, post) ==> pre ->
forall s,    pre s -> (vcPre s /\ (forall (s :State)  (a : Assertion), Pre a -> a s)) .
Proof with auto.
intros Sj post vcPre Pre Hj.
induction Hj; intros Sm Htr pre Hm s Hpre.

inversion Htr; subst.
inversion Hm; subst; split; intros...
intuition.

apply triche. (* Seq *)

(* Affect *)
inversion Htr; subst.
inversion Hm; subst; split; intros...
intuition.

(* If *)
inversion Htr; subst.
inversion Hm; subst; split; intros...
destruct Hpre.
split; intros.
assert(h := IHHj1 _ H2 _ H7 s (H H1)).
destruct h...

assert(h := IHHj2 _ H4 _ H6 s (H0 H1)).
destruct h...

destruct Hpre.
assert(h1 := IHHj1 _ H2 _ H7 s).
assert(h2 := IHHj2 _ H4 _ H6 s).
destruct (neval s b)...
assert(h3: pre_f s); auto; assert(h4 :=  h2 h3); destruct h4.
apply H5; intuition.
destruct h...

eapply IHHj2.
intuition.

