(* Esc Java  - Coq extension  Sorted logic. *)


Require Import Bool.
Require Import ZArith.
Require Import Zdiv.
Require Import Zbool.
Require Import Reals.
Require Import Classical.
Open Scope Z_scope.

(* LA tactique primitive *)
Ltac genclear H := generalize H;clear H.

(* Variable S: Set. *)
Definition Time := Z.
Definition t_int := Z.
Definition t_long := Z.
Definition t_float := R.
Definition t_double := R.
Variable Types : Set.
Inductive S: Set  := 
       Z_to_S : Z -> S.
Definition LockSet := S.
Definition Path := S.
Definition Reference:= S.

Definition Elem := Reference.
Definition Field := Reference.
(* Some arithmetic things *)
Variable S_to_Z : S -> Z.
(* Variable Z_to_S : Z -> S. *)
Axiom Z_to_S_elim : forall x,  S_to_Z (Z_to_S x) = x.
Variable S_to_bool : S -> bool.

Variable S_false : S.
Variable S_true : S.
Axiom S_false_is_false : S_to_bool S_false = false.
Axiom S_true_is_true : S_to_bool S_true = true.
Hint Rewrite S_false_is_false S_true_is_true: escj.
Axiom S_to_Z_det: 
         forall x : S,  (S_to_Z x) = (S_to_Z x).
Lemma S_to_Z_inj:
         forall x y: Z, (Z_to_S x) = (Z_to_S y) -> x = y.
Proof.
intros x y H.
injection H.
trivial.
Qed.
Axiom S_to_bool_det: 
         forall x y: S,  x = y -> (S_to_bool x) = (S_to_bool y).
Hint Immediate S_to_Z_det S_to_bool_det.
Hint Rewrite Z_to_S_elim:escj.

Lemma Zeq_bool_sym :
forall x:Z, Zeq_bool x x = true.
Proof ( fun x => @eq_ind_r 
                   comparison Eq (fun c => (match  c with Eq => true | _ => false end) = true) 
                                 (refl_equal true) (x ?= x) (Zcompare_refl x)).

Lemma Zeq_bool_true:
forall x y: Z, x = y ->Zeq_bool x y = true.
Proof fun x y H  => eq_ind_r (fun x0 : Z => Zeq_bool x0 y = true) (Zeq_bool_sym y) H.


Lemma Zeq_bool_false:
forall x y: Z, x <> y ->Zeq_bool x y = false.
Proof
fun x y H =>
match Zcompare_Eq_iff_eq x y with
| conj a _ => 
      let c := x ?= y in
      match c return ((c = Eq -> x = y) -> 
                                  match c with Eq => true| _ => false end = false)
      with 
      | Eq => fun h =>
            match H (h (refl_equal Eq)) return (true = false) with end 
      | _ => fun _ => refl_equal false
       end a
end.


Lemma negb_elim :
    forall b, negb (negb b) = b.
Proof fun b  => sym_eq (negb_intro b).


Ltac subst_S_to :=
repeat match goal with 
|[ H: S_to_bool ?x = _ |- _] =>
      let v := fresh "X" in (set (v := S_to_bool x) in *; clearbody v; subst v)
|[ H: S_to_Z ?x = _ |- _] =>
      let v := fresh "X" in (set (v := S_to_bool x) in *; clearbody v; subst v)
end.

Hint Rewrite negb_elim :escj.
Hint Resolve Zeq_bool_sym Zeq_bool_true Zeq_bool_false.

Definition integralGE : Z -> Z -> Prop := fun (x y : Z) => x >= y.
Definition integralGT : Z -> Z -> Prop := fun (x y : Z) =>  x > y.
Definition integralLE : Z-> Z -> Prop := fun (x y : Z) => x <= y.
Definition integralLT : Z -> Z -> Prop := fun (x y : Z) => x < y.

Definition integralEQ_bool : Z -> Z -> bool := fun (x y : Z) => Zeq_bool x  y.
Definition integralGE_bool : Z -> Z -> bool := fun (x y : Z) => Zge_bool x y.
Definition integralGT_bool : Z -> Z -> bool := fun (x y : Z) => Zgt_bool x y.
Definition integralLE_bool : Z -> Z -> bool := fun (x y : Z) =>  Zle_bool x y.
Definition integralLT_bool : Z -> Z -> bool := fun (x y : Z) => Zlt_bool x y.

Definition integralDiv : Z -> Z -> Z := 
             fun (x y : Z) =>(x  / y).
Definition integralAdd : Z -> Z -> Z := 
             fun (x y : Z) =>(x  + y).
Definition integralSub : Z -> Z -> Z := 
             fun (x y : Z) =>(x - y).
Definition integralMul : Z -> Z -> Z := 
             fun (x y : Z) =>(x  * y).
Definition integralNeg : Z -> Z := 
             fun (x : Z) =>(0 - x).
Ltac unfoldEscArith := unfold  integralEQ_bool, integralGE_bool, integralLE_bool, integralGT_bool, integralLT_bool, integralGE, integralLE, integralGT, integralLT, integralAdd, integralSub, integralMul, integralNeg in *.





Variable null : Reference.
Variable isAllocated: Reference -> Time -> Prop.
Variable fClosedTime : S -> S.
Variable vAllocTime : Reference -> Time.

Variable ecReturn : S.
Variable ecThrow : S.
Axiom distinctAxiom : ecReturn <> ecThrow.
Hint Immediate distinctAxiom.

(* The following are grabbed from Jack's Coq Plugin *)
Variable refEQ : Reference -> Reference -> bool.
Axiom refEQ_refl : forall x, refEQ x x = true. 
Axiom refEQ_eq : forall x y, refEQ x y = true -> x = y. 
Lemma refEQ_eq_true : forall x y, x = y-> refEQ x y = true.
Proof fun x y (H : x = y) =>
           eq_ind_r (fun x0 => refEQ x0 y = true) (refEQ_refl y) H.

Lemma refEQ_eq_not_false : forall x y, x=y-> refEQ x y <> false.
Proof fun x y  (e : x = y) => eq_ind_r (fun b  => b <> false)
  (fun H : true = false =>  False_ind False (eq_ind true 
          (fun ee => if ee then True else False) I false H)) 
      (refEQ_eq_true x y e).

Lemma refEQ_false_not_eq :  forall x y, refEQ x y = false -> x <> y.
Proof fun x y H e => refEQ_eq_not_false x y e H.

Definition exists_refEQ_eq : forall x y, {b:bool  | refEQ x y = b}.
Proof  fun x y  => let H := refEQ x y in exist (fun b => H = b) H (refl_equal H).

Lemma not_eq_false_refEQ : forall x y, x <> y -> refEQ x y = false.
Proof fun x y H => not_true_is_false  (refEQ x y) (fun h  => H (refEQ_eq x y h)).

(* End of the stolen part *)




Hint Rewrite refEQ_refl : escj.
 

Variable subtypes: Types -> Types-> Prop.
Variable typeof : Reference -> Types.
Variable lockLT : LockSet -> LockSet -> Prop.
(*Variable is : S -> S -> Prop. *)
Variable isField : Field -> Prop.
Variable allocNew_ : Reference.


Variable asField: Field -> Types -> Prop.
Variable asElems: Elem -> Elem.
Variable asLockSet: LockSet -> LockSet.

Variable eClosedTime: S -> t_int.

(* Array Logic *)
Variable arrayShapeOne: t_int -> Reference.
Variable arrayShapeMore: t_int-> Reference -> Reference.
Variable isNewArray: Reference -> Prop.
Variable arrayLength: Reference -> t_int.
Axiom arrayLengthAx :
      forall (a : Reference), (integralLE 0 (arrayLength a)).
Variable unset: S -> Z -> Z -> S.

(* The operations on the heap - more or less *)
Module Type Heap .
Parameter A : Set.
Variable arrselect: S -> Z -> A.
Variable arrstore: S -> Z -> A -> S.

Variable select: S -> A -> S.
Variable store: S -> A -> S -> S.

Axiom select_store1: 
    forall(var val :S)(obj :A), (select (store var obj val) obj) = val.
Axiom select_store2: 
    forall(var val :S)(obj1 obj2 :A), 
         obj1 <> obj2 -> 
                 (select (store var obj1 val) obj2) = (select var obj2).
Variable arrayFresh : Reference -> Time -> Time -> S -> S -> Types -> A -> Prop.

(* array axioms2 *)
Axiom array_axiom2 : 
      forall (a: Reference) ( a0:Time) (b0:Time) (e : S) (n : t_int)  (T: Types)  (v : A),
        ((arrayFresh a a0 b0 e (arrayShapeOne n)  T v) ->
         (a0 <= (vAllocTime a))) /\
        ((arrayFresh a  a0  b0 e (arrayShapeOne n) T v) ->
         (isAllocated a  b0)) /\
        ((arrayFresh a  a0  b0 e (arrayShapeOne n) T v) ->
         (a <> null)) /\
        ((arrayFresh a  a0  b0 e (arrayShapeOne n) T v) ->
         (typeof a) = T) /\
        ((arrayFresh a  a0  b0 e (arrayShapeOne n) T v) ->
         (arrayLength a) = n) (* /\
        ((arrayFresh a  a0  b0 e (arrayShapeOne n) T v) ->
         forall (i : Reference),
           (select (select e a) i) = v) *).

(* maybe another day... Hint Resolve array_axiom2_2 array_axiom2_3 array_axiom2_4 array_axiom2_5 array_axiom2_6. *)

Ltac unfoldArrAx_intern R :=
         match goal with
          | [H : (arrayFresh ?a  ?a0  ?b0 ?e (arrayShapeOne ?n) ?T ?v) |- _ ] =>
               let H1 := fresh "H" in (assert (H1 :=  (array_axiom2 a a0  b0  e  n  T  v H)));
                genclear H; unfoldArrAx_intern R
          | [H: _ |- _ ] => genclear H; unfoldArrAx_intern R
          | _ => intros
        end.

Ltac unfoldArrAx  :=
         match goal with
          | [H : _|- ?R ] =>  unfoldArrAx_intern R
        end.

Ltac arrtac := (* a ameliorer *)
match goal with
| [H1: (arrayFresh null  ?a0  ?b0 ?e (arrayShapeOne ?n) ?T ?v) |- _] => 
                 let H:= fresh "H" in (assert (H :=  (array_axiom2 null a0  b0  e  n  T  v H1)); repeat (destruct H); trivial)
| [H1: (arrayFresh ?a  ?a0  ?b0 ?e (arrayShapeOne ?n) ?T ?v) |- _] => 
                 let H:= fresh "H" in (assert (H :=  (array_axiom2 null a0  b0  e  n  T  v H1)); repeat (destruct H); trivial)
end.


End Heap.

Module Type A_args. 
Parameter A : Set .
End A_args.

Module    AHeap (X:A_args): Heap with Definition A := X.A   .
Definition A := X.A.
Variable arrselect: S -> Z -> A.
Variable arrstore: S -> Z -> A -> S.

Variable select: S -> A -> S.
Variable store: S -> A -> S -> S.

Axiom select_store1: 
    forall(var val :S)(obj :A), (select (store var obj val) obj) = val.
Axiom select_store2: 
    forall(var val :S)(obj1 obj2 :A), 
         obj1 <> obj2 -> 
                 (select (store var obj1 val) obj2) = (select var obj2).
Variable arrayFresh : Reference -> Time -> Time -> S -> S -> Types -> A -> Prop.
(* array axioms2 *)
Axiom array_axiom2 : 
      forall (a: Reference) ( a0:Time) (b0:Time) (e : S) (n : t_int)  (T: Types)  (v : A),
        ((arrayFresh a a0 b0 e (arrayShapeOne n)  T v) ->
         (a0 <= (vAllocTime a))) /\
        ((arrayFresh a  a0  b0 e (arrayShapeOne n) T v) ->
         (isAllocated a  b0)) /\
        ((arrayFresh a  a0  b0 e (arrayShapeOne n) T v) ->
         (a <> null)) /\
        ((arrayFresh a  a0  b0 e (arrayShapeOne n) T v) ->
         (typeof a) = T) /\
        ((arrayFresh a  a0  b0 e (arrayShapeOne n) T v) ->
         (arrayLength a) = n) (* /\
        ((arrayFresh a  a0  b0 e (arrayShapeOne n) T v) ->
         forall (i : Reference),
           (select (select e a) i) = v) *).

(* maybe another day... Hint Resolve array_axiom2_2 array_axiom2_3 array_axiom2_4 array_axiom2_5 array_axiom2_6. *)

Ltac unfoldArrAx_intern R :=
         match goal with
          | [H : (arrayFresh ?a  ?a0  ?b0 ?e (arrayShapeOne ?n) ?T ?v) |- _ ] =>
               let H1 := fresh "H" in (assert (H1 :=  (array_axiom2 a a0  b0  e  n  T  v H)));
                genclear H; unfoldArrAx_intern R
          | [H: _ |- _ ] => genclear H; unfoldArrAx_intern R
          | _ => intros
        end.

Ltac unfoldArrAx  :=
         match goal with
          | [H : _|- ?R ] =>  unfoldArrAx_intern R
        end.

Ltac arrtac := (* a ameliorer *)
match goal with
| [H1: (arrayFresh null  ?a0  ?b0 ?e (arrayShapeOne ?n) ?T ?v) |- _] => 
                 let H:= fresh "H" in (assert (H :=  (array_axiom2 null a0  b0  e  n  T  v H1)); repeat (destruct H); trivial)
| [H1: (arrayFresh ?a  ?a0  ?b0 ?e (arrayShapeOne ?n) ?T ?v) |- _] => 
                 let H:= fresh "H" in (assert (H :=  (array_axiom2 null a0  b0  e  n  T  v H1)); repeat (destruct H); trivial)
end.

End AHeap.


Module ArgRef : A_args with Definition A := Reference.
Definition A := Reference.
End ArgRef.

Module RefHeap := AHeap ArgRef.
Hint Resolve RefHeap.select_store2.
Hint Rewrite  -> RefHeap.select_store1 : escj_select.


Module ArgInt : A_args with Definition A := t_int.
Definition A := t_int.
End ArgInt.

Module IntHeap := AHeap ArgInt.
Hint Resolve IntHeap.select_store2.
Hint Rewrite  -> IntHeap.select_store1 : escj_select.

Module ArgBool : A_args with Definition A := bool.
Definition A := bool.
End ArgBool.

Module BoolHeap := AHeap ArgBool.
Hint Resolve BoolHeap.select_store2.
Hint Rewrite  -> BoolHeap.select_store1 : escj_select.








(* Sans elimOr/elimAnd c'est un peu la deche *)
(**
 ** elimAnd
 elimAnd is used mainly to eliminate and within the hypothesis.
For the goals the preferred tactic is still split.

*)


Ltac map_hyp Tac :=
  repeat match goal with
    | [ H : _ |- _ ] => try (Tac H);genclear H
    end; intros.

Inductive Plist : Prop :=
  | Pnil : Plist
  | Pcons : Prop -> Plist -> Plist.

Ltac build_imp Pl C :=
  match Pl with
  | Pnil => constr:C
  | Pcons ?A ?Pl' =>
        let C' := constr:(A->C) in
        build_imp Pl' C'
  end.

Inductive PPlProd : Prop :=
 | PPlPair : Plist -> Prop -> PPlProd.

Ltac elim_aT Pl T :=
  match T with
  | ?A /\ ?B =>
      let A' := elim_aT Pl A in
      let B' := elim_aT Pl B in
      constr:(A' /\ B')
  | ?A => build_imp Pl T
  end.
Ltac elim_iaT Pl T :=
   match T with
   | (?B /\ ?C) =>
        let P := elim_aT Pl T in
        constr:(PPlPair Pl P)
   | (?A -> ?D) =>
        let Pl' := constr:(Pcons A Pl) in
        elim_iaT Pl' D
   end.

Ltac splitAndH H :=
  match type of H with
  | ?A /\ ?B =>
             case H;clear H;
             let H1 := fresh "H" in
             let H2 := fresh "H" in
             (intros H1 H2; splitAndH H1; splitAndH H2)
  | _ => idtac
  end.
Ltac introPl Pl H :=
 match Pl with
 | Pnil => splitAndH H
 | Pcons _ ?pl =>
     let H1 := fresh "H" in
     let H2 := fresh "H" in
     (intro H1;assert (H2 := H H1);introPl pl H2)
 end.

Ltac splitAnd :=
  match goal with
  | [|- ?A /\ ?B] => split;splitAnd
  | _ => idtac
  end.
Ltac elimAnd :=
  match goal with
  | [H : ? A /\ ?B |- _ ] =>
             case H;clear H;
             let H1 := fresh "H" in
             let H2 := fresh "H" in
             intros H1 H2; elimAnd
  | [H : ?HT|- _ ] =>
       let pair := elim_iaT Pnil HT in
       match pair with
       | PPlPair ?Pl ?newT =>
         assert newT;
         [splitAnd; introPl Pl H;trivial
         | clear H;elimAnd]
       end
  | [H: _ |- _ ] => genclear H;elimAnd
  | _ => intros; repeat match goal with [H: _ |- _ /\ _] => split end
  end.

(**
 ** elimNor
This tactic is used to remove the not in front of a or (in the hypothesis),
turning [~ (A \/  B) ] into [(~ A) /\ (~ B)].

*)

Definition distr_or : forall A B, ~ (A \/ B) ->  ~ A.
Proof fun A B a b => False_ind False (a (or_introl B b)).

Definition distr_or_inv : forall A B, ~ (A \/ B) ->  ~B.
Proof fun A B a b => False_ind False (a (or_intror A b)).

Ltac elimNorCons a b := let H1 := fresh "H" in
                                          assert (H1 : ~ (a)); cut (~(a \/ b)) ; auto;
                                          let H2 := fresh "H" in
                                          assert (H2 : ~ (b)); cut (~(a \/ b)); auto.

Ltac elimNor :=
  repeat match goal with
  |   [H: ~ (?a \/ ?b) |- _ ] => elimNorCons a b; clear H;  let H0 := fresh "H" in (let H1 := fresh "H" in  (intros H0 H1; clear H0 H1))
end.

Ltac elim_or H HT R:=
        match HT with
           | ?A \/ R =>
                 let h := fresh "H" in assert(h : A \/  R); [apply H; intros; auto | idtac]
         | R\/ ?B  =>
                 let h := fresh "H" in assert(h : R \/  B); [apply H; intros; auto |idtac]
           |  ?C -> ?D => elim_or H D R
        end.

Ltac solve_or R :=
         match goal with
          | [H : R \/ ?B |-_ ] => destruct H; auto; try contradiction; intros
          | [H : ?A \/ R |- _ ] => destruct H;  auto; try contradiction; intros
          | [H : ?HT|- _ ] => elim_or H HT R; genclear H;solve_or R
          | [H: _ |- _ ] => genclear H; solve_or R
          | _ => intros
        end.

Ltac solveOr :=
         match goal with
          | [H : _|- ?R ] =>  solve_or R
        end.

Ltac simplOr_rec h name tail :=
        match h with
        |    ?A \/ ?B -> ?C  => assert(tail -> A -> C); [intros; apply name;trivial; left;trivial| idtac];
                                                        assert(tail -> B -> C); [intros; apply name; trivial; right;trivial| idtac]; clear name
        |    ?A -> ?B => simplOr_rec B name (tail -> A)
        end.

Ltac simplOr_im h name :=
        match h with
        |    ?A \/ ?B -> ?C  => assert(A -> C); [intros; apply name; left;trivial| idtac];
                                                        assert(B -> C); [intros; apply name; right;trivial| idtac]; clear name
        |    ?A -> ?B => simplOr_rec B name A
        end.
Ltac simplOr :=
        repeat match goal with
        |   [H: ?A |- _] =>simplOr_im A H
        end.

Ltac elimOr := simplOr.





(**
 ** Cleansing
To clean up the mess (sometimes).

*)
Lemma a_ou_a_donne_a: forall a : Prop, a \/ a -> a.
Proof fun a H => match H return a with
                             | or_introl H0 => H0
                             | or_intror H0 => H0
                             end.


Ltac cleanUp :=
repeat match goal with
| [H: True |- _] => clear H
| [H1: ?a, H2: ?a |- _] => clear H2
| [H1: ?a = ?a |- _ ] => clear H1
| [ H: ?a \/ ?a |- _] => let H1 := fresh "H" in (assert(H1 := a_ou_a_donne_a a H); clear H)
| [H1: ?a < ?b, H2: ?a <= ?b |- _] => clear H2
end.



Ltac autosc := intros; subst; elimOr; elimAnd; intros; subst;  
repeat match goal with
|[H: _ |- _] => rewrite RefHeap.select_store1 in H
end;
repeat match goal with
|[H: _ |- _] => rewrite BoolHeap.select_store1 in H
end; autorewrite with escj; auto.
Ltac startsc := unfold not; unfoldEscArith; autorewrite with escj; autorewrite with escj_select; intros; subst.
(* unfoldArrAx. *)



