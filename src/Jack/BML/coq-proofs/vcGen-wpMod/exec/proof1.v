Require Import semantique.
Require Import wpMod.
Require Import wp.
Require Import Ensembles.
Require Import List.


Reserved Notation "'j2m' s1 ==> s2" (at level 30).
Inductive Stmt_jToStmt_m : Stmt Invariant_j -> Stmt Invariant_m -> Prop :=
| Stmt_j2mSkip : j2m (Skip Invariant_j) ==>  (Skip Invariant_m)
| Stmt_j2mAffect : forall v val, 
                    j2m (Affect Invariant_j v val) ==> (Affect Invariant_m v val)
| Stmt_j2mIf : forall b t t' f f', 
                   j2m t ==> t' -> j2m f ==> f' -> 
                   j2m (If Invariant_j b t f) ==>  (If Invariant_m b t' f')
| Stmt_j2mWhile : forall b i  s s' (l: list Var), 
              (forall x, In x l) -> j2m s ==> s' -> 
              j2m (While Invariant_j b (inv_j i) s) ==>  (While Invariant_m b (inv_m i l) s')
| Stmt_j2mSeq : forall s1 s1' s2 s2', 
                   j2m s1 ==> s1' -> j2m s2 ==> s2' -> 
                   j2m (Seq Invariant_j s1 s2) ==>  (Seq Invariant_m s1' s2')
where "'j2m' s1 ==> s2" :=   (Stmt_jToStmt_m s1 s2).



Lemma imp1:
forall (post: Assertion) pre Sm,    wpMod(Sm, post) ==> pre ->
forall Sj, j2m Sj ==> Sm ->
forall  vcPre (Pre : Ensemble Assertion), 
 (vcGen(Sj, post) ==> (vcPre, Pre)) ->
forall s,   (vcPre s /\ (forall (s :State)  (a : Assertion), Pre a -> a s))  -> pre s.
Proof with auto.

intros post  pre Sm  Hm.
induction Hm; intros Sj Htr  vcPre Pre Hj.

(* Skip *)
intros;
destruct H;
inversion Htr; subst;
inversion Hj; subst...

(* Affect *)
intros;
destruct H;
inversion Htr; subst;
inversion Hj; subst...

(* If *)
intros;
destruct H;
inversion Htr; subst;
inversion Hj; subst...
destruct H.
split.
intros;
apply IHHm2 with t pT PT...
split...
intros; apply H0; apply Union_introl...

intros.
apply IHHm1 with f pF PF...
split...
intros; apply H0; apply Union_intror...


(* While *)
intros.
inversion Htr; subst.
inversion Hj;
unfold Cs, Ci in H7; subst...
repeat split...
intros x h; destruct h...
destruct H...
destruct H.
intros st_fin.
assert (h0 := H0 st_fin (fun s : State => vcPre s /\ neval s bExp = 0 -> post s)).
assert(h1 : (fun s : State => vcPre s /\ neval s bExp = 0 -> post s) st_fin); [apply h0 | idtac].
apply Union_introl; intuition.
intros h2 h3 h4; simpl in h1.
apply h1; split; trivial.

intros st_ h0 h1 h2.
apply IHHm with s0 pI PI...
apply vcGen_monotone with vcPre. intros; split...
intros.
destruct H1...
destruct H; auto.
destruct H.  
assert (h3 := H0 st_ (fun s : State => vcPre s /\ neval s bExp <> 0 -> pI s)).
assert(h4 : (fun s : State => vcPre s /\ neval s bExp <> 0 -> pI s) st_); [apply h3 | idtac].
apply Union_introl; intuition.
simpl in h4...
split; auto.


intros s1 a h5.
apply H0; apply Union_intror...



(* Seq *)
inversion Htr; subst...
inversion Hj; subst...
intros.
destruct H.
apply IHHm2 with s1 vcPre P1...
2: split...
apply vcGen_monotone with p2...
intros.
apply IHHm1 with s2 p2 P2...
split...
intros; apply H0; apply Union_intror...
intros; apply H0; apply Union_introl...

Qed.