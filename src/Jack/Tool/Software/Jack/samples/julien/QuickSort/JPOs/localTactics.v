(* I am the third little helper. *)

(** * The Local Tactics Library *)

Open Scope J_Scope.
(**
 ** elimAnd
 elimAnd is used mainly to eliminate and within the hypothesis.
For the goals the preferred tactic is still split.

*)

Ltac genclear H := generalize H;clear H.
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

(** ** SolveInc
SolveInc was once used to solve trivial incrementations and
some arithmetic stuff; it is a bit like a light j_omega

*)
Lemma j_le_inc_sup : forall n m v, (Zle 0 n) -> (j_le m v) -> (j_le m (j_add v n)).
Proof with auto.
unfold j_le, j_add in *; intros.
replace m with (((m - n)+ n)%Z).
apply Zplus_le_compat_r. assert (((m - n) <= m)%Z).
omega.
apply Zle_trans with m...
omega.
Qed.

Lemma j_le_inc_inf : forall m v, (j_lt v m) -> (j_le (j_add v 1) m).
Proof with auto.
unfold j_le, j_lt, j_add  in *; intros.
replace (v  + 1)%Z with (Zsucc v). apply Zlt_le_succ...
omega.
Qed.

Lemma j_ge_le: forall n m, (j_le m n) -> (j_ge n m).
Proof with auto.
unfold j_ge, j_le; intros.
apply Zle_ge...
Qed.

Lemma j_le_ge: forall n m, (j_ge m n) -> (j_le n m).
Proof with auto.
unfold j_ge, j_le; intros.
apply Zge_le...
Qed.

Lemma j_gt_lt: forall n m, (j_lt m n) -> (j_gt n m).
Proof with auto.
unfold j_gt, j_lt; intros.
apply Zlt_gt...
Qed.

Lemma j_lt_gt: forall n m, (j_gt m n) -> (j_lt n m).
Proof with auto.
unfold j_gt, j_lt; intros.
apply Zgt_lt...
Qed.

Lemma j_not_gt_hyp: forall n m, (~ (j_gt m n)) -> (j_le m n).
Proof with auto.
unfold j_gt, j_le; intros; apply Znot_gt_le...
Qed.
Lemma j_not_gt: forall n m, (j_le m n) -> (~ (j_gt m n)).
Proof with auto.
unfold j_gt, j_le; intros; apply Zle_not_gt...
Qed.
Lemma j_not_ge_hyp: forall n m, (~ (j_ge m n)) -> (j_lt m n).
Proof with auto.
unfold j_ge, j_lt; intros; apply Znot_ge_lt...
Qed.
Lemma j_not_ge: forall n m, (j_lt m n) -> (~ (j_ge m n)).
Proof with auto.
unfold j_ge, j_lt.
intros n m H1 H2.  apply H2. assumption.
Qed. 

Lemma j_not_lt_hyp: forall n m, (~ (j_lt m n)) -> (j_ge m n).
Proof with auto.
unfold j_lt, j_ge; intros; apply Znot_lt_ge...
Qed.
Lemma j_not_lt: forall n m, (j_ge m n) -> (~ (j_lt m n)).
Proof with auto.
unfold j_lt, j_ge; intros n m H1 H2; apply H1; assumption.
Qed.
Lemma j_not_le_hyp: forall n m, (~ (j_le m n)) -> (j_gt m n).
Proof with auto.
unfold j_le, j_gt; intros; apply Znot_le_gt...
Qed.
Lemma j_not_le: forall n m, (j_gt m n) -> (~ (j_le m n)).
Proof with auto.
unfold j_le, j_gt; intros n m H1 H2.  apply H2. assumption.
Qed.

Lemma j_le_dec_sup : forall m v, (j_lt m v) -> (j_le (j_sub v 1) m) -> m = (j_sub v 1).
Proof with auto.
unfold j_le, j_lt, j_sub  in *; intros m v h1 h2.
assert (h3:(v <= m + 1)%Z).
rewrite <- (Zplus_0_r v). rewrite <- (Zplus_opp_l 1). rewrite Zplus_assoc.
apply Zplus_le_compat_r. assumption.
replace (m  + 1)%Z with (Zsucc m) in h3.
assert(h4 : (Zsucc m <= v)%Z).
apply Zlt_le_succ...
apply Zle_antisym; omega. omega.
Qed.
Ltac solve_hyp f t H m n :=
let H1 := fresh "H" in (assert (H1: f m n) ; [(apply t; assumption; clear H)|clear H]).

Ltac solveInc :=
repeat match goal with 
|  [H: (j_lt ?v ?w) |- (j_le (j_add ?v 1) ?w)] => apply j_le_inc_inf;apply H
|  [H1: (j_le ?m ?n), H2: j_le ?n  ?m |- _] => 
                      let H := fresh "H" in (assert (H: m = n); 
                         [(apply Zle_antisym; auto; clear H1; clear H2) | (clear H1; clear H2)])
|  [H: (j_ge ?n ?m) |- _] => solve_hyp j_le j_le_ge H m n
|  [H: _ |- (j_ge ?n ?m)] => apply j_ge_le
|  [H: (j_gt ?n ?m) |- _] => solve_hyp j_lt j_lt_gt H m n
|  [H: _ |- (j_gt ?n ?m)] => apply j_gt_lt
|  [H: ~ (j_gt ?n ?m) |- _] => solve_hyp j_le j_not_gt_hyp H n m
|  [H: _ |- ~ (j_gt ?n ?m)] => apply j_not_gt
|  [H: ~ (j_ge ?n ?m) |- _] => solve_hyp j_lt j_not_ge_hyp H n m
|  [H: _ |- ~ (j_ge ?n ?m)] => apply j_not_ge
|  [H: ~ (j_lt ?n ?m) |- _] => solve_hyp j_ge j_not_lt_hyp H n m
|  [H: _ |- ~ (j_lt ?n ?m)] => apply j_not_lt
|  [H: ~ (j_le ?n ?m) |- _] => solve_hyp j_gt j_not_le_hyp H n m
|  [H: _ |- ~ (j_le ?n ?m)] => apply j_not_le
|  [H: _ |- j_le ?n ?n] => unfold j_le; apply Zle_refl
end.

(**
 ** elimNor
This tactic is used to remove the not in front of a or (in the hypothesis),
turning [~ (A \/  B) ] into [(~ A) /\ (~ B)]. 

*)

Definition distr_or : forall A B, ~ (A \/ B) ->  ~ A.
 intros A B a b.
 elim a; trivial.  left; trivial.
Qed.

Definition distr_or_inv : forall A B, ~ (A \/ B) ->  ~B.
 intros A B a b.
 elim a; trivial.  right; trivial.
Qed.

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

(**
 ** overriding; elimIF
These tactics are more for internal use; eliminating overriding constructions
and the hypothesis using REFeq and Zeq.

*)

Ltac elimREFeq x y :=
let H1 := fresh "H" in
let H2 := fresh "H" in
let H3:= fresh "H" in
(assert (H1 := REFeq_eq x y);
assert (H2 := REFeq_false_not_eq x y);
destruct (REFeq x y);
[assert (H3  := H1 (refl_equal true));clear H1 H2; try (subst x)
| assert (H3 := H2 (refl_equal false));clear H1 H2]).

Ltac overriding := 
	  match goal with
	  | [H : ?a <> ?c |- overridingCoupleRef ?T ?f ?a ?b ?c = ?f ?c] =>
	            apply  overridingCoupleRef_diff; apply H
	  | [H : ?a = ?c |- overridingCoupleRef ?T ?f ?a ?b ?c = ?b] =>
	            apply  overridingCoupleRef_eq; apply H
	  | [H : ?a <> ?c |- overridingCoupleZ ?T ?f ?a ?b ?c = ?f ?c] =>
	            apply  overridingCoupleZ_diff; apply H
	  | [H : ?a = ?c |- overridingCoupleZ ?T ?f ?a ?b ?c = ?b] =>
	            apply  overridingCoupleZ_eq; apply H
	  end.
Ltac EQ_is_eq :=
  repeat match goal with
  | [H : REFeq ?x ?y = true |- _ ] =>
           let H1 := fresh "H" in 
           (assert (H1 :=  REFeq_eq x y H);clear H)
  |  [H : REFeq ?x ?y = false |- _ ] =>
           let H1 := fresh "H" in 
           (assert (H1 :=  REFeq_false_not_eq x y H); clear H)
  | [H : Zeq ?x ?y = true |- _ ] =>
           let H1 := fresh "H" in 
           (assert (H1 :=  Zeq_eq x y H);clear H)
  |  [H : Zeq ?x ?y = false |- _ ] =>
           let H1 := fresh "H" in 
           (assert (H1 :=  Zeq_false_not_eq x y H); clear H)
   end.
 Ltac generalize_all x :=
	match goal with
   | [H : context [x] |- _ ] => generalize H;clear H; generalize_all x
   | _ => idtac
   end.

 Ltac gendestruct x :=
   generalize_all x;
   generalize (refl_equal x);
   pattern x at -1;
   case x.
 Ltac elimIF :=
   repeat match goal with
   | [H : context  [REFeq ?x ?x] |- _ ] => rewrite (REFeq_refl x) in H
   | [H1 : REFeq ?x ?y = false, H2 : context [if (REFeq ?x ?y) then _ else _] |- _]  => 
      rewrite H1 in H2
   | [H1 : REFeq ?x ?y = true, H2 : context [if (REFeq ?x ?y) then _ else _]  |- _] => 
       rewrite H1 in H2
   | [H : context  [Zeq ?x ?x] |- _ ] => rewrite (Zeq_refl x) in H
   | [H1 : Zeq ?x ?y = false, H2 : context [if (Zeq ?x ?y) then _ else _] |- _]  => 
      rewrite H1 in H2
   | [H1 : Zeq ?x ?y = true, H2 : context [if (Zeq ?x ?y) then _ else _]  |- _] => 
       rewrite H1 in H2
   | [H : context [if ?b then _ else _ ]|- _] => gendestruct b;intros
   | [|- context [if ?b then _ else _]] => gendestruct b;intros
    end;EQ_is_eq;subst.
 

(**
 ** Array Things
Old Tactics used in the tactic arrtac.

*)

Ltac unfoldRefArrAx array pos := let H:= fresh "H" in (assert(H := refelementsDom (refelements array pos)  array pos);
                                                                 let H1 := fresh "H" in (assert (H1 : refelements array pos = null \/  instances (refelements array pos));
                                                                                     [apply H; trivial | clear H])).

Ltac unfoldArrayTypeAx arr := match goal with
[H: (subtypes (typeof ?arr) (array (class ?c) ?n)) |- _] =>
                   let H1:= fresh "H" in (assert(H1 := ArrayTypeAx arr c n);
                                              let H2 := fresh "H" in (assert (H2 := H1 H); clear H))
end.

Ltac solveRefElm := match goal with
| [h : _ |- instances (refelements ?array ?pos)] =>
                              unfoldRefArrAx array pos
end.

(**
 ** Cleansing
To clean up the mess (sometimes).

*)

Ltac clean_up :=
repeat match goal with
| [H1: ?a, H2: ?a |- _] => clear H2| [H1: ?a = ?a |- _ ] => clear H1| [H1: ?a < ?b, H2: ?a <= ?b |- _] => clear H2
end.

(**
 ** Absurd
When there is a contradiction absurdJack can often solve it. It is mainly used
through autoJack.

 *)

Ltac absurdJack := 
  match goal with
  | [H : true = false |- _] => inversion H
  | [H : false = true |- _] => inversion H
  | [H : ?x <> ?x |- _ ] => elim H;trivial 
  | [H1 : ?x <> ?y, H2 : ?x = ?y |- _] => elim (H1 H2)
  | [H: Zpos _ < 0 |- _] => discriminate H
  | [H: Zpos _ <= 0 |- _]=> elim H;trivial
  | [H : subtypes _ _ |- _ ] => simpl in H; match type of H with False => elim H end
  | [H1 : arraylength ?x = _, H2 : context [j_sub (arraylength ?x) _] |- _] =>
        rewrite H1 in H2;simpl in H2;absurdJack
  | [H : ?x -> subtypes _ _ |- _ ] =>
    simpl in H;
    match type of H with _ -> False => elim H; auto end
  | _ => try discriminate
  end.
Ltac absurdJackTougher := 
  match goal with
  | [H : ?x -> subtypes _ _ |- _ ] =>
  simpl in H;
 match type of H with _ -> False => elim H; auto end
  | _ => idtac
  end.
(**
 ** Some Macros
 *** j_omega
it is used for arithmetic solving on java types.
 *** solveOver
it is used to simplify overriding constructions.

*)

Ltac j_omega := try (unfold j_le, j_add, j_mul, j_lt, j_sub in *; omega).
Ltac solveOver := 
        unfold overridingCoupleZ, overridingCoupleRef in *; elimIF.
 

(**
 ** Automatic proving
 *** autoJack
Jack's CoqPlugin's auto tactic.
 *** tryApply
To automatically solve a goal applying an hypothesis.
 *** startJack
To prepare things up (doing some intros; unfolding several things).
 *** light and tough AutoJack
Used for automatic proving.

*)

Ltac autoJack := 
   auto;
   try overriding;
   try absurdJack;
   try (solveOver;auto;absurdJack).

Ltac tryApply :=
  match goal with 
  | [ H : _ |- _ ] => ((intros;apply H;autoJack) || (generalize H;clear H;tryApply))
  | _ => intros
 end.

Ltac Folie := do 2 (elimIF; tryApply; autoJack; intuition; autoJack).

Ltac lightStartJack := intros; unfold singleton, union, functionEquals, interval in *; elimAnd; elimNor.
Ltac lightAutoJack := lightStartJack; autoJack; try j_omega.

Ltac toughAutoJack := lightStartJack; Folie.

 Ltac startJack := lightStartJack; solveInc; clean_up.


(**
 ** destrJlt
Used to destruct loops: when you have [i <= b] and you want to have two cases:
[i < b] and [i = b].

*)

Ltac destrJlt n :=
    let H := fresh "H" in (assert (H: n); [j_omega | idtac]; destruct (j_le_lt_or_eq _ _ H); auto).

(**
 ** Some more array tactics
 *** arrlen
 To use when you have things to prove on the length of arrays.
 *** arrtype
 To use when you have things to prove on the subtypes of arrays.
 *** arrelm
 To use when a goal has the form [instance (refelements arr i)].
 *** arrtac
 An auto tactic for arrays using all of the above.

*)

Ltac arrlen :=
   eapply arraylenAx; eauto.
Ltac arrtype := eapply ArrayTypeAx; eauto.
Ltac arrelm := solveRefElm; autoJack.

Ltac find_subtype_array t T :=
    match T with
    | subtypes (typeof t) (array _ _) => constr:T
    | ?A -> ?B => find_subtype_array t B
    end.

Ltac assertsubtypes_array t :=
    match goal with
    | [H: ?T |- _] => 
      match find_subtype_array t T with
      |  ?res => assert (res); [apply H | intros;arrlen]
      end
    end.

Ltac le_arraylength :=
  match goal with
  | [|- 0 <= arraylength ?t] =>
     assertsubtypes_array t
  end.

Ltac array_tac :=
  match goal with
  | [|- instances (refelements _ _)] => arrelm
  | [|- subtypes (typeof (refelements _ _)) _] => arrtype
  | [|- 0 <=  arraylength ?t] =>
     assertsubtypes_array t; try array_tac
  | _ => idtac
  end.

Ltac arrtac := array_tac.

