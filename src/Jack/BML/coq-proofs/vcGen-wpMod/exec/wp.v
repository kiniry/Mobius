
Require Import  semantique.
Require Import List.
Reserved Notation "'vcGen' ( a , p )  ==> ( b , c )" (at level 30).

Inductive wp : Stmt Invariant_j  -> Assertion -> Assertion -> list Assertion -> Set:=
| wpSkip: forall a, vcGen(Skip Invariant_j, a) ==>  (a, nil)
| wpSeq: forall i1 i2 a p2 P2 p1 P1, 
                    vcGen(i2, a) ==> (p2, P2) -> vcGen(i1, p2) ==> (p1, P1) ->
                                         vcGen(Seq Invariant_j i1 i2, a) ==> 
                                                                  (p1, (P1 ++ P2 ))
| wpAffect: forall a v exp, 
                           vcGen ((Affect Invariant_j v exp), a) ==> 
                                           ((fun s => a (update s v (neval s exp))), nil)
| wpIf: forall pT PT pF PF a b t f, vcGen( t, a) ==> (pT, PT) -> vcGen(f, a) ==> (pF, PF) ->
                         vcGen (If Invariant_j b t f, a) ==> ((fun s => p_and (p_implies (p_neq (neval s b) 0) (pT s) ) 
                                          (p_implies (p_eq (neval s b)  0) (pF s))),
                           (PT ++ PF ))
| wpWhile: forall i inv pI PI b (a: Assertion), vcGen(i, inv) ==> (pI, PI) -> 
             let Cs := fun s => (p_implies (p_and  (inv s)  (p_neq (neval s b) 0))  (pI s)) in
             let Ci := fun s => (p_implies (p_and (inv s) (p_eq (neval s b)  0)) (a  s) ) in
              vcGen(While Invariant_j b (inv_j inv)  i, a) ==>
                   (inv,  ( Cs :: nil) ++ (Ci :: nil)  ++ PI )
where " 'vcGen' ( a , p ) ==> ( b , c ) " := (wp a p b c) .



Notation "S |- l ==> l1  " := ((execBs Invariant_j) l S  l1) (at level 30).
Notation " |- P" := (forall l : State, P l) (at level 30).


Lemma corr:
forall S  (l l': State), 
(S |- l ==> l' ) -> forall (post : Assertion ) p (P: list Assertion),
vcGen(S, post) ==>  (p, P) ->
(forall a: Assertion, In a P   ->  forall s: State,  (evalMyProp (a s))) ->
evalMyProp ( p l) ->
evalMyProp (post l').
Proof with auto.
intros S l l' Hi.
induction Hi.

(* Skip *)
intros.
inversion H; subst...

(* Affect *)
intros.
inversion H; subst...

(* If true *)
intros.
inversion H; subst...
simpl in H1.
destruct H1.
apply (IHHi _ _ _ H8)...
intros; 
apply H0; intuition.

(* If false *)
intros.
inversion H; subst...
simpl in H1.
destruct H1.
apply (IHHi _ _ _ H9)...
intros; 
apply H0; intuition.

(* While false *)
intros.
inversion H.
unfold Cs, Ci in H7; clear Cs Ci; subst.
assert(h :=  H0 (fun s : State =>
          p_implies (p_and (p s) (p_eq (neval s b) 0)) (post s))).
assert(forall s : State,
    evalMyProp
      ((fun s0 : State =>
        p_implies (p_and (p s0) (p_eq (neval s0 b) 0)) (post s0)) s)).
apply h; intuition.
assert(h1:= H2 s); simpl in h1.
apply h1...

(* While true *)
intros.
inversion H;
unfold Cs, Ci in H7; clear Cs Ci; subst.
apply (IHHi2 _ _ _ H)...
apply (IHHi1 _ _ _ H8)...
intros; apply H0; intuition.
assert(h :=  H0 (fun s : State =>
           p_implies (p_and (p s) (p_neq (neval s b) 0)) (pI s))).
assert(forall s : State,
    evalMyProp
      ((fun s0 : State =>
        p_implies (p_and (p s0) (p_neq (neval s0 b) 0)) (pI s0)) s)).
apply h; intuition.
assert(h1:= H2 s); simpl in h1.
apply h1...


(* Seq *)
intros.
inversion H; subst.
apply (IHHi2 _ _ _ H4)...
intros; apply H0; intuition.
apply (IHHi1 _ _ _ H8)...
intros; apply H0; intuition.
Qed.


Lemma wpCons :
forall S (post post' pre' pre : Assertion) Vcs' Vcs,
 vcGen(S, post') ==> (pre', Vcs') -> (forall s,  (post' s -> post s)) ->(forall s, (pre' s -> pre s) ) ->
 vcGen(S, post) ==> (pre, Vcs).
intros S.
induction S.
intros post post' pre' pre Vcs' Vcs.
intros H.

elim H.
inversion H; subst.
(* intros S.
induction S; 
intros post post' pre' pre Vcs' Vcs.
intros.
inversion H; subst.
injection H0. *)
Lemma vcGen_monotone:
forall S, forall (p1  p2 : Assertion)  ,  (forall s, (p1 s -> p2 s)) -> forall pre P, ((vcGen(S, p1) ==> (pre, P)) -> vcGen(S, p2) ==> (pre, P)) .
Proof with auto.
intros.


intros S p1 p2 Himp.
induction S.
intros pre P H.
generalize (refl_equal p2).
pattern p2 at -1.
elim H.

pattern p2 at 1 .
elim H.
intros.
injection.
inversion H; subst.
intros...
intuition.
elim H.
pattern p2 at 1.
elim p2.
intros.
 Himp.
induction S.
generalize (refl_equal p2).
pattern p2 at -1 -2.

case p2.
intros pre P H.
induction S.
injection.
intros.
apply wpCons with p1 pre P...
Qed.
