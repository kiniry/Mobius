Require Import ZArith.

Variable P : Z -> Prop.
Variable Q: Z -> Z -> Prop.

Lemma sequence : 
(forall g0, exists g1, ( P g1 /\ Q g0 g1) )->
(exists g1, P g1) /\ forall g0, exists g1, (Q g0 g1).
Proof.
intros.
split.
assert (B := H 1%Z).
elim B.
intros.
destruct H0.
exists x.
assumption.

intros.
assert ( B := H g0).
elim B.
intros.
destruct H0.
exists x.
assumption.

Qed.