Require Import semantique.
Require Import wpMod.
Require Import wp.
Require Import Ensembles.
Require Import List.


Reserved Notation "'m2j' s1 ==> s2" (at level 30).
Inductive Stmt_mToStmt_j : Stmt Invariant_m -> Stmt Invariant_j -> Prop :=
| Stmt_m2jSkip : m2j (Skip Invariant_m) ==>  (Skip Invariant_j)
| Stmt_m2jAffect : forall v val, m2j (Affect Invariant_m v val) ==>
(Affect Invariant_j v val)
| Stmt_m2jIf : forall b t t' f f', m2j t ==> t' -> m2j f ==> f' -> m2j
(If Invariant_m b t f) ==>  (If Invariant_j b t' f')

| Stmt_m2jWhile : forall b i  s s' (l: list Var), (forall x, In x l)
-> m2j s ==> s' -> 
m2j (While Invariant_m b (inv_m i l) s) ==> (While Invariant_j b (inv_j i) s') 

| Stmt_m2jSeq : forall s1 s1' s2 s2', m2j s1 ==> s1' -> m2j s2 ==> s2' -> m2j
(Seq Invariant_m s1 s2) ==>  (Seq Invariant_j s1' s2')

where "'m2j' s1 ==> s2" :=   (Stmt_mToStmt_j s1 s2).

Axiom triche: forall p: Prop, p.

Lemma imp1:
forall postM pre Sm, wpMod(Sm, postM) ==> pre ->
forall Sj, j2m Sj ==> Sm ->
forall postJ vcPre (Pre : Ensemble Assertion),
 (vcGen(Sj, postJ) ==> (vcPre, Pre)) ->
forall s, (forall s, postJ s -> postM s) -> (vcPre s /\ (forall (s :
State)  (a : Assertion), Pre a -> a s))  -> pre s.
Proof with auto.
intros post pre Sm Hmod.
induction Hmod.

(* Skip *)
intros.
inversion H; subst.
inversion H0; subst.
destruct H2...

(* Affect *)
intros.
inversion H; subst.
inversion H0; subst.
destruct H2.

unfold update_assert...

(* If *)
intros.
inversion H; subst.
inversion H0; subst.
destruct H2.
destruct H2.

split.
(* case true *)
intros.
apply IHHmod2 with t postJ pT PT...
split...
intros.
assert(h := H3 s0 a).
apply h.
apply Union_introl...

(* case false *)
intros.
apply IHHmod1 with f postJ pF PF...
split...
intros.
assert(h := H3 s0 a).
apply h.
apply Union_intror...

(* case while *)
intros.
inversion H; subst.
repeat split...
intros.
destruct H3; apply H6...
destruct H2.
inversion H0;
unfold Cs, Ci in H11; clear Cs Ci; subst...

(* case = 0 *)
intros.
inversion H0;
unfold Cs, Ci in H13; clear Cs Ci; subst...
destruct H2.
assert(h := H7 st_fin (fun s : State => vcPre s /\ neval s bExp = 0 ->
postJ s)).
assert((fun s : State => vcPre s /\ neval s bExp = 0 -> postJ s) st_fin).
apply h; apply Union_introl; intuition.
simpl in H8.
apply H1.
apply H8...

(* case <> 0 *)
intros.
inversion H0;
unfold Cs, Ci in H13; clear Cs Ci; subst...
apply IHHmod with s0 vcPre pI PI...
intros; split...
intros...
destruct H8...
destruct H2.
assert(h := H7 st_ (fun s : State => vcPre s /\ neval s bExp <> 0 -> pI s)).
assert((fun s : State => vcPre s /\ neval s bExp <> 0 -> pI s) st_).
 apply h; apply Union_introl; intuition.
split...
intros; apply H7; apply Union_intror; intuition.


(* Seq *)
intros.
inversion H; subst.
inversion H0; subst.
apply IHHmod2 with t p2 vcPre P1...
intros.
apply IHHmod1 with f postJ p2 P2...
split...
destruct H2.
intros.
apply H4.
apply Union_intror...
destruct H2...
split...
intros.
apply H3.
apply Union_introl...
Qed.