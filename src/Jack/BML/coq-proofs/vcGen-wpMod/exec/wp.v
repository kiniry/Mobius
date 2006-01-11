
Require Import  semantique.
Require Import List.
Reserved Notation "'vcGen' ( a , p )  ==> ( b , c )" (at level 30).

Inductive wp : Stmt Invariant_j  -> Assertion -> Assertion -> list Assertion -> Prop:=
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
                   (inv,  ( Cs :: Ci ::  PI ))
where " 'vcGen' ( a , p ) ==> ( b , c ) " := (wp a p b c) .
Definition pres (l:list Assertion) :=
  match l with
  | nil => EmptyAssertion 
  | x :: L => x
  end.
Definition vcs (l:list Assertion) :=
  match l with
  | nil => EmptyAssertion :: nil
  | x :: L => L
  end.
Fixpoint VcGen  (S: Stmt Invariant_j)  (post: Assertion) {struct S}: list Assertion  :=
match S with
| Skip => post:: nil
| Affect v exp => ((fun s => post (update s v (neval s exp))):: nil)
| If b t f => let resT := (VcGen t post) in 
                  let pT := pres resT in
                  let PT := vcs resT in
                  let resF := (VcGen f post) in 
                  let pF := pres resF in
                  let PF := vcs resF in
            ((fun s => p_and (p_implies (p_neq (neval s b) 0) (pT s) ) 
                                          (p_implies (p_eq (neval s b)  0) (pF s)))::  (PT ++ PF ))
| While b (inv_j inv) i =>
         let resI := (VcGen i inv) in
         let pI := pres resI in
         let PI := vcs resI in
            let Cs := fun s => (p_implies (p_and  (inv s)  (p_neq (neval s b) 0))  (pI s)) in
             let Ci := fun s => (p_implies (p_and (inv s) (p_eq (neval s b)  0)) (post s) ) in
            (inv ::  ( Cs :: nil) ++ (Ci :: nil)  ++ PI )
| Seq i1 i2 => let res2 := (VcGen i2 post) in 
                        let p2 :=  pres res2 in 
                        let P2 := vcs res2 in
                        let res1 := (VcGen i1 p2) in
                        let p1 :=  pres res1 in 
                        let P1 := vcs res1 in
                       (p1:: (P1 ++ P2 ))
end.


(* Notation " S |- l ==> l1  " := ((execBs Invariant_j) l S  l1) (at level 160). *)
Notation " |- P" := (forall l : State, P l) (at level 30).


Lemma corr:
forall S  (l l': State), 
(execBs Invariant_j  l S  l' ) -> forall (post : Assertion ) p (P: list Assertion),
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
Lemma vcg_decomp :
forall S post, 
VcGen S post = pres ( VcGen S post) :: vcs ( VcGen S post).
Proof with auto.
intros S.
elim S;
intros;
try apply refl_equal.
simpl in |- *.
unfold pres.
case (i)...
Qed.
Hint Immediate vcg_decomp.
Lemma equivVcGen : 
forall S, forall post p P, VcGen S post = p :: P  <-> vcGen(S, post) ==> (p, P).
Proof with auto.
intro S.
induction S; split; intros.


(* Skip *)
simpl in H.
injection H; intros. 
rewrite <- H0;
rewrite <- H1.
apply wpSkip.
inversion H.
simpl in |- *; auto.

(* Affect *)

simpl in H; injection H; intros.
rewrite <-  H0; rewrite <- H1.
apply wpAffect.
inversion H.
simpl in |- *; auto.


(* If *)
generalize H.
simpl in H.
intros.
injection H.
intros.
rewrite <-  H2; rewrite <- H1.
apply wpIf.
assert (h :=IHS1 post (pres (VcGen S1 post)) (vcs (VcGen S1 post))); destruct h.
apply H3; apply vcg_decomp.
assert (h :=IHS2 post (pres (VcGen S2 post)) (vcs (VcGen S2 post))); destruct h.
apply H3; apply vcg_decomp.
(* If 2 *)
simpl in |- *; auto.
inversion H.
clear H4 H5; subst.
assert (h_1 :=IHS1 post (pT) (PT)); destruct h_1.
assert(h1 := H1 H6); rewrite h1.
assert (h_2 :=IHS2 post (pF) (PF)); destruct h_2.
assert(h2 := H3 H7); rewrite h2...

(* While 1 *)
simpl in H.
destruct i.
injection H.
intros.
rewrite <- H0; rewrite <- H1.

apply wpWhile.
assert(h := IHS a (pres (VcGen S a)) (vcs (VcGen S a))); destruct h.
apply H2.
apply vcg_decomp.

(* While 2 *)
simpl in |- *.
inversion H.
unfold Cs, Ci in H5;  unfold Cs, Ci ; clear Cs Ci.
assert(h := IHS p pI PI); destruct h.
subst.
(* rewrite H1.*)
assert(h1:= H8 H6).
rewrite h1...

(* Seq 1 *)
simpl in H.
injection H; intros.
rewrite <- H0; rewrite <- H1.
apply wpSeq with (pres (VcGen S2 post)).
assert(h := IHS2 post  (pres (VcGen S2 post)) (vcs (VcGen S2 post))); destruct h.
apply H2.
apply vcg_decomp.
assert(h := IHS1 (pres (VcGen S2 post))
(pres (VcGen S1 (pres (VcGen S2 post))))
(vcs (VcGen S1 (pres (VcGen S2 post))))); destruct h.
apply H2.
apply vcg_decomp.

(* Seq 2 *)
simpl in |-  *.
inversion H.
assert(h_1 := IHS2 post p2 P2); destruct h_1.
assert(h1:= H8 H2).
rewrite h1.
assert(h_2 := IHS1 p2 p P1); destruct h_2.
assert(h2 := H10 H6).
simpl in |- *.
rewrite h2...
Qed.
Axiom triche: forall p: Prop, p.

Lemma vcGen_monotone1:
forall S, forall (p1  p2 pre1 pre2 : Assertion) ,  (forall s, (evalMyProp (p1 s) -> evalMyProp (p2 s))) -> forall P1 P2, (VcGen S p1) = (pre1:: P1) -> (VcGen S p2) = (pre2:: P2) -> (forall s, (evalMyProp (pre1 s) -> evalMyProp (pre2 s))) .
Proof with auto.
intros S.
induction S;

intros; simpl in H0; simpl in H1;

repeat match goal with 
| [ H : _ = _ |-  _ ]  => injection H; clear H
end;
intros;

 subst...
simpl in H2.
destruct H2.
simpl; split.
intros h; assert(h1:= H0 h).
eapply IHS1 ; eauto.
intros h; assert(h1:= H1 h).
eapply IHS2; eauto.


injection H1.
case i; intros inv; intros.

repeat match goal with 
| [ H : _ = _ |-  _ ]  => injection H; clear H
end;
intros;
 subst...

apply triche.
eapply IHS1 with (p2 :=  (pres (VcGen S2 p2))) (P2 := (vcs (VcGen S1 (pres (VcGen S2 p2))))); eauto.
Qed.

Lemma vcGen_monotone2:
forall S, forall (p1  p2 pre1 pre2: Assertion)  ,  (forall s, (evalMyProp (p1 s) -> evalMyProp (p2 s))) -> forall P1 P2, vcGen(S, p1) ==> (pre1, P1) -> vcGen( S, p2) ==> (pre2, P2) -> (forall s, (evalMyProp (pre1 s) -> evalMyProp (pre2 s))) .
Proof with auto.
intros.
apply (vcGen_monotone1  S _ _ pre1 pre2 H P1 P2)...
assert(h := (equivVcGen S p1 pre1 P1)); destruct h...
assert(h := (equivVcGen S p2 pre2 P2)); destruct h...
Qed.

Axiom vcGen_monotone:
forall S, forall (p1  p2 : Assertion)  , forall pre P, ((vcGen(S, p1) ==> (pre, P)) -> (forall s, (evalMyProp (p1 s) -> evalMyProp (p2 s))) ->  vcGen(S, p2) ==> (pre, P)).

(* Proof with auto.
intros until P.
intro H.
induction H.
intros.
eapply wpSkip.
induction S.
inversion H0.
destruct pre.
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
*)