
(* Objects Definitions *)
Inductive Types : Set :=
    class : Classes -> Types 
|   array : Types -> Z -> Types.


Variable REFERENCES : Set.
Variable null : REFERENCES.
Variable instanceof : REFERENCES -> Types -> Prop.


Variable STRING : Set.
Variable j_string : STRING -> REFERENCES.
Variable instances : REFERENCES -> Prop.
Axiom nullInstances : (not (instances null)).


Variable typeof : REFERENCES -> Types.
Variable REFeq : REFERENCES -> REFERENCES -> bool.
Variable REFeq_refl : forall x, REFeq x x = true. 
Variable REFeq_eq : forall x y, REFeq x y = true -> x = y. 
Lemma REFeq_eq_true : forall x y, x = y-> REFeq x y = true.
Proof.
intros x y H. rewrite H. apply REFeq_refl.
Qed. 
Lemma REFeq_eq_not_false : forall x y, x=y-> REFeq x y <> false.
Proof.
intros x y e. rewrite REFeq_eq_true; trivial; discriminate.
Qed. 
Lemma REFeq_false_not_eq :  forall x y, REFeq x y = false -> x <> y.
Proof.
exact (fun x y H e => REFeq_eq_not_false x y e H).
Qed. 
Definition exists_REFeq_eq : forall x y, {b:bool  | REFeq x y = b}.
Proof.
 intros. exists (REFeq x y). constructor.
Qed. 
Lemma not_eq_false_REFeq : forall x y, x <> y -> REFeq x y = false.
Proof.
 intros x y H. apply not_true_is_false.
 intro. apply H. apply REFeq_eq. assumption.
Qed. 
Lemma eq_dec : forall (x y:REFERENCES), {x = y} + {x <> y}.
Proof.
 intros x y; case (exists_REFeq_eq x y). intros b; case b; intro H.
 left; apply REFeq_eq; assumption. right; apply REFeq_false_not_eq ; assumption.
Qed.
Lemma Zeq_refl : forall x, Zeq x x = true.
Proof.
 intros; unfold Zeq; rewrite Zcompare_refl; trivial.
Qed.
Lemma Zeq_eq : forall x y, Zeq x y = true -> x = y.
 intros x y H; apply Zeq_prop; rewrite H; exact I.
Qed.
Lemma Zeq_eq_true: forall x y, x = y -> Zeq x y = true.
Proof.
 intros x y H;rewrite H;apply Zeq_refl.
Qed.
Lemma not_eq_false_Zeq : forall x y, x<>y -> Zeq x y = false.
Proof.
 intros x y H; assert (H1 := Zeq_prop x y);destruct (Zeq x y);trivial.
 elim H; apply H1;exact I.
Qed.
Lemma Zeq_false_not_eq :  forall x y, Zeq x y = false -> x <> y.
Proof.
 intros x y H1 H2; rewrite H2 in H1; rewrite Zeq_refl in H1; discriminate H1.
Qed. 
Definition singleton (a:Set) (r s:a) := r = s :> a.
Definition union (s:Set) (a b:s -> Prop) (c:s) := (a c) \/ (b c).
Definition equalsOnOldInstances (s:Set) (f g:REFERENCES->s) :=forall x:REFERENCES, (instances x) -> (f x) = (g x) :> s.
Definition intersectionIsNotEmpty (s:Set)(f g:s->Prop) := (exists y : _, (f y) /\ (g y)).

Definition  overridingCoupleRef (T:Set) (f:REFERENCES -> T)(a:REFERENCES) (b:T) (c:REFERENCES) := if (REFeq a c) then b else (f c).
Lemma overridingCoupleRef_diff : forall T f a b c, a <> c -> overridingCoupleRef T f a b c = f c.
Proof. intros; unfold overridingCoupleRef; rewrite not_eq_false_REFeq; trivial. Qed.
Lemma overridingCoupleRef_eq : forall T f a b c, a = c -> overridingCoupleRef T f a b c = b.
Proof. intros; unfold overridingCoupleRef; rewrite REFeq_eq_true; trivial. Qed.
Definition  overridingCoupleZ (T:Set) (f:Z -> T)(a:Z) (b:T) (c:Z) := if (Zeq a c) then b else (f c).
Lemma overridingCoupleZ_diff : forall T f a b c, a <> c -> overridingCoupleZ T f a b c = f c.
Proof. intros; unfold overridingCoupleZ; rewrite not_eq_false_Zeq; trivial. Qed.
Lemma overridingCoupleZ_eq : forall T f a b c, a = c -> overridingCoupleZ T f a b c = b. 
Proof.
 intros T f a b c H; unfold overridingCoupleZ; rewrite (Zeq_eq_true _ _ H); trivial.
Qed.

Variable overridingArray : forall s t u:Set, (s->t->u)->(s->Prop)->(t->Prop)->u->s->t->u.
Axiom overridingArray_t_t : forall (s t u: Set) (f: s->t->u) (a: s->Prop) (b: t->Prop) (c: u) (x: s) (y: t), (a x) -> (b y) -> ((overridingArray s t u f a b c x y) = c :> u).
Axiom overridingArray_t_f : forall (s t u: Set) (f: s->t->u) (a: s->Prop) (b: t->Prop) (c: u) (x: s) (y: t), (a x) -> ~(b y) -> ((overridingArray s t u f a b c x y) = (f x y) :> u).
Axiom overridingArray_f : forall (s t u: Set) (f: s->t->u) (a: s->Prop) (b: t->Prop) (c: u) (x: s) (y: t), ~(a x) -> ((overridingArray s t u f a b c x y) = (f x y) :> u).
Definition setEquals (s: Set) (f g: s->Prop) := forall x: s, (f x) -> (g x) /\ (g x) -> (f x).
Definition functionEquals (s t: Set)(f g: s->t) := forall x: s, ((f x) = (g x) :> t).
Definition interval (a b: Z) (c: Z) := (j_le a c) /\ (j_le c b).
Variable question : forall t: Type, Prop -> t -> t -> t.
Axiom question_t : forall (t: Set) (x: Prop) (y z: t), x -> ((question t x y z) = y :> t).
Axiom question_f : forall (t: Set) (x: Prop) (y z: t), ~x -> ((question t x y z) = z :> t).


(* Time to play with the arrays. *)
Variable elemtype : Types -> Types.
Definition elemtypeDomDef (t:Types): Prop :=
    match t with
    |    (class _) => False 
    |    (array cl n) => (1 <= n)
    end.
Axiom elemtypeAx : forall (c : Types) (n : Z), (1 <= n) -> 
   ((elemtype (array c n)) = (array c (n - 1))).

Variable arraylength : REFERENCES -> t_int.
Variable intelements : REFERENCES -> t_int -> t_int.
Definition intelementsDomDef (r:REFERENCES): Prop := (instances r) /\ ((typeof r) = (array (class c_int) 1) :> Types).
Variable shortelements : REFERENCES -> t_int -> t_short.
Definition shortelementsDomDef (r:REFERENCES): Prop := (instances r) /\ ((typeof r) = (array (class c_short) 1) :> Types).
Variable charelements : REFERENCES -> t_int -> t_char.
Definition charelementsDomDef (r:REFERENCES): Prop := (instances r) /\ ((typeof r) = (array (class c_char) 1) :> Types).
Variable byteelements : REFERENCES -> t_int -> t_byte.
Definition byteelementsDomDef (r:REFERENCES): Prop := (instances r) /\ ((typeof r) = (array (class c_byte) 1) :> Types).
Variable booleanelements : REFERENCES -> Z -> bool.
Axiom boolelementsDomDef : forall (r:REFERENCES), (instances r) /\ ((typeof r) = (array (class c_boolean) 1)).
Variable refelements : REFERENCES -> Z -> REFERENCES.
Axiom refelementsDom : forall r a b, r = refelements a b -> (r = null \/ instances r).
