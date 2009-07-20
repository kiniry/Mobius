Lemma L : forall ( A : Set  ) (P1: A -> Prop)  P2 ,
    ( exists x:A , (P1 x  /\ P2  ) ) ->  (exists x:A , P1 x  ) /\ P2  . 
Proof.
  intros. 
  elim H. 
  intros.
  split. exists x.
  intuition.
  intuition.
Qed.

Lemma M : forall ( A : Set  ) (P1: A -> Prop)  P2 ,
     (exists x:A , P1 x  ) /\ P2 -> ( exists x:A , (P1 x  /\ P2  ) )  . 
Proof.
  intros.
  destruct H.
  elim H. intros.
  exists x.
  split.
  intuition.
  intuition.
Qed.

Lemma N : forall A B C P : Prop,
	((A /\ B) -> C) ->
	( (P-> A) /\ B  ) -> (P -> C).
Proof.
  intros.
  apply  H.
  split.
  destruct H0.
  apply H0.
  assumption.
  destruct H0.
  assumption.
Qed.