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

Definition Time := Z.
Definition int := Z.
Definition long := Z.
Definition float := R.
Definition double := R.
Variable Types : Set.
Definition LockSet := Z.
Variable Path : Set.
Definition Reference:= Z.
Definition Elem := Reference.
Definition Field := Reference.

Inductive S: Set  := 
	|   bool_to_S: bool -> S
    |   int_to_S : int -> S
    |   long_to_S: long -> S
    |   float_to_S: float -> S
    |   double_to_S: double -> S
    |   Reference_to_S: Reference -> S.
Coercion bool_to_S : bool >-> S.
Coercion int_to_S : int >-> S.
Coercion long_to_S : long >-> S.
Coercion float_to_S : float >-> S.
Coercion double_to_S : double >-> S.
Coercion Reference_to_S : Reference >-> S.


Definition S_to_bool (s:S): bool :=
match s with 
| bool_to_S b => b
| _ => false
end.
Coercion S_to_bool : S >-> bool.

Definition S_to_int (s:S): int :=
match s with 
| int_to_S b => b
| _ => 0%Z
end.
Coercion S_to_int : S >-> int.

Definition S_to_long (s:S): long :=
match s with 
| long_to_S b => b
| _ => 0%Z
end.
Coercion S_to_long : S >-> long.

Definition S_to_float (s:S): float :=
match s with 
| float_to_S b => b
| _ => 0%R
end.
Coercion S_to_float : S >-> float.


Definition S_to_double (s:S): double :=
match s with 
| double_to_S b => b
| _ => 0%R
end.
Coercion S_to_double : S >-> double.

Definition null : Reference := 0.

Definition S_to_Reference (s:S): Reference :=
match s with 
| Reference_to_S b => b
| _ => null
end.
Coercion S_to_Reference : S >-> Reference.




Lemma negb_elim :
    forall b, negb (negb b) = b.
Proof fun b  => sym_eq (negb_intro b).

Module Type Arith.
Parameter t: Set.

Variable EQ_bool : t -> t -> bool.

Variable GE : t -> t -> Prop.
Variable GT : t -> t -> Prop.
Variable LE : t -> t -> Prop.
Variable LT : t -> t -> Prop.

Variable GE_bool : t -> t -> bool.
Variable GT_bool : t -> t -> bool.
Variable LE_bool : t -> t -> bool.
Variable LT_bool : t -> t -> bool.

Variable Div :  t -> t -> t.
Variable Add : t -> t -> t.
Variable Sub : t -> t -> t.
Variable Mul : t -> t -> t.
Variable Neg : t ->  t.

Variable EQ_bool_sym :
        forall x: t, EQ_bool x x = true.
Variable EQ_bool_true:
        forall x y: t, x = y -> EQ_bool x y = true.
Variable EQ_bool_false:
        forall x y: Z, x <> y ->Zeq_bool x y = false.
End Arith.

Module Int <: Arith.
Definition t := int.
Definition GE : int -> int -> Prop := fun (x y : Z) => x >= y.
Definition GT : int -> int -> Prop := fun (x y : Z) =>  x > y.
Definition LE : int-> int -> Prop := fun (x y : Z) => x <= y.
Definition LT : int -> int -> Prop := fun (x y : Z) => x < y.
Definition EQ_bool : int -> int -> bool := fun (x y : Z) => Zeq_bool x  y.
Definition GE_bool : int -> int -> bool := fun (x y : Z) => Zge_bool x y.
Definition GT_bool : int -> int -> bool := fun (x y : Z) => Zgt_bool x y.
Definition LE_bool : int -> int -> bool := fun (x y : Z) =>  Zle_bool x y.
Definition LT_bool : int -> int -> bool := fun (x y : Z) => Zlt_bool x y.
Definition Div :  int -> int -> int := 
             fun (x y : Z) =>(x  / y).
Definition Add : int -> int -> int := 
             fun (x y : Z) =>(x  + y).
Definition Sub : int -> int -> int := 
             fun (x y : Z) =>(x - y).
Definition Mul : int -> int -> int := 
             fun (x y : Z) =>(x  * y).
Definition Neg : int -> int := 
             fun (x : Z) =>(0 - x).
Lemma EQ_bool_sym :
forall x:Z, EQ_bool x x = true.
Proof ( fun x => @eq_ind_r 
                   comparison Eq (fun c => (match  c with Eq => true | _ => false end) = true) 
                                 (refl_equal true) (x ?= x) (Zcompare_refl x)).

Lemma EQ_bool_true:
forall x y: Z, x = y ->EQ_bool x y = true.
Proof fun x y H  => eq_ind_r (fun x0 : Z => Zeq_bool x0 y = true) (EQ_bool_sym y) H.

Lemma EQ_bool_false:
forall x y: Z, x <> y -> EQ_bool x y = false.
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
End Int.



Ltac unfoldEscArith := unfold  Int.EQ_bool, Int.GE_bool, 
                                                     Int.LE_bool, Int.GT_bool, Int.LT_bool, 
                                                     Int.GE, Int.LE, Int.GT, Int.LT, 
                                                     Int.Add, Int.Sub, Int.Mul, Int.Neg in *.



Definition cast : Reference -> Types -> Reference := 
 fun (v:Reference)  (t: Types) => v.
Variable fClosedTime : Field -> Time.

Variable vAllocTime : Reference -> Time.
Definition isAllocated: Reference -> Time -> Prop := 
    fun (obj : Reference) (t: Time) => vAllocTime obj < t.
Ltac unfoldEscTime := unfold isAllocated.
Variable ecReturn : Path.
Variable ecThrow : Path.
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
Variable alloc_ : Reference.


Variable asField: Field -> Types -> Prop.
Variable asElems: Elem -> Elem.
Variable asLockSet: LockSet -> LockSet.

Variable eClosedTime: Elem -> Time.

(* Array Logic *)
Variable arrayShapeOne: int -> Reference.
Variable arrayShapeMore: int-> Reference -> Reference.
Variable isNewArray: Reference -> Prop.
Variable arrayLength: Reference -> int.
Axiom arrayLengthAx :
      forall (a : Reference), (Int.LE 0 (arrayLength a)).
(* Variable unset: S -> Z -> Z -> S. *)

(* The operations on the heap - more or less *)
Module Heap.
Variable arrselect: Reference -> int -> S.
Variable arrstore: Reference -> int -> S -> Reference.
Variable select: Reference -> Reference -> S.
Variable store: Reference -> Reference ->  S -> Reference.

Axiom select_store1: 
    forall(var obj : Reference)(val : S), (select (store var obj val) obj) = val.
Axiom select_store2: 
    forall(var obj1 obj2 :Reference) (val :  S), 
         obj1 <> obj2 -> 
                 (select (store var obj1 val) obj2) = (select var obj2).
Axiom arrselect_store1: 
    forall(var :Reference) (obj : int)(val :S), (arrselect (arrstore var obj val) obj) = val.
Axiom arrselect_store2: 
    forall(var : Reference)(obj1 obj2 :int) (val :  S), 
         obj1 <> obj2 -> 
                 (arrselect (arrstore var obj1 val) obj2) = (arrselect var obj2).

Variable arrayFresh : Reference -> Time -> Time -> S -> Reference -> Types ->  S (* A *) -> Prop.

(* array axioms2 *)
Axiom array_axiom2 : 
      forall (array: Reference) ( a0:Time) (b0:Time) (obj : Reference) (n : int)  (T: Types)  (v :  S),
        ((arrayFresh array a0 b0 obj (arrayShapeOne n)  T v) ->
         (a0 <= (vAllocTime array))) /\
        ((arrayFresh array  a0  b0 obj (arrayShapeOne n) T v) ->
         (isAllocated array  b0)) /\
        ((arrayFresh array  a0  b0 obj (arrayShapeOne n) T v) ->
         (array <> null)) /\
        ((arrayFresh array  a0  b0 obj (arrayShapeOne n) T v) ->
         (typeof array) = T) /\
        ((arrayFresh array  a0  b0 obj (arrayShapeOne n) T v) ->
         (arrayLength array) = n) (* /\
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


Hint Resolve Heap.select_store2.
Hint Rewrite  -> Heap.select_store1 Heap.arrselect_store1: escj_select.


Coercion Is_true : bool >-> Sortclass.

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



Ltac simplsc := intros; subst; elimOr; elimAnd; intros; subst; 
try match goal with
| [H: context a [negb (negb _)] |- _] =>
	rewrite negb_elim in H
end;
repeat match goal with
|[H: _ |- _] => rewrite Heap.select_store1 in H
end;
 autorewrite with escj; autorewrite with escj_select;
auto.
Ltac startsc := unfoldEscTime; unfoldEscArith; autorewrite with escj; autorewrite with escj_select; intros; subst.
(* unfoldArrAx. *)
Ltac autosc := simplsc;
repeat match goal with
| [ H: ?v = ?v -> _ |- _ ] =>
     let h := fresh "H" in
       assert(h := H (refl_equal ecReturn));
       clear H; try subst
end;
try match goal with 
| [ H: (~ True) = True |- _ ] => 
       let h := fresh "H" in
        (assert(h := I); rewrite <- H in h; apply h); exact I
end.

Definition jVar := Z.
Variable ivar : jVar -> int.
Require Import List.
Inductive jProp : Set :=
| jforall : list jVar -> jProp-> jProp
| jtrue : jProp
| jfalse : jProp
| jimply : jProp -> jProp -> jProp.

(* Notation "A -> B" := (jimply A B) (at level 70) : jProp_scope. *)

(* Notation "'forall' f" := (jforall f) (at level 70): jProp_scope. *)


Definition jLemma := ((list jProp) * jProp)%type.

Definition simplify : list jProp -> jProp -> jLemma := fun l p => (l, p).

Fixpoint interpProp (p : jProp) {struct p} :  Prop :=
match p with
| jforall l p => interpProp p
| jtrue => True
| jfalse => False
| jimply p1 p2 => (interpProp p1) -> interpProp p2
end.
Fixpoint interp_hypos (l: list jProp) (g: jProp) {struct l} : Prop :=
match l with
| cons a L => (interp_hypos L a) -> interpProp g
| nil => interpProp g
end.

Definition interp (pr: jLemma): Prop :=
match pr with
   pair l g => interp_hypos l g
end.

Lemma eval : forall l p, interp (pair l p) -> interp (simplify l p).
Proof with auto.
intros.
simpl in *.
assumption.
Qed.


