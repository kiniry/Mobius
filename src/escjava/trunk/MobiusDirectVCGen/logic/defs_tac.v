


Ltac genclear H := generalize H; clear H.




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




Ltac startsc := autorewrite with escj; autorewrite with escj_select; intros; subst.




Ltac myred := 
 hnf;match goal with
 | [|- _ -> _] => intro;hnf;myred
 | [|- _ /\ _] => split;hnf;myred
 | _ => idtac
 end.

Ltac simpl_hyps := 
 match goal with 
 | [H : _ /\ _ |- _ ] => 
    let h1 := fresh "H" in let h2 := fresh "H" in destruct H as (h1,h2);simpl_hyps
 | [H:SemCompInt _ _ _ |- _] => simpl in H;simpl_hyps
 | [H:METHOD.valid_var _ _ |- _ ] => clear H;simpl_hyps
 | [H:compat_ValKind_value _ _ |- _] => clear H;simpl_hyps
 | _ => idtac
  end.
Ltac my_simpl :=
 simpl interp_swp in *;
 simpl interp_initstate in *;
 simpl interp_localstate in *;
 simpl interp_returnstate in *;
 simpl interp_wptype in *;
 simpl interp_assert in *;
(* simpl top in *;*)
 simpl fst in *;
 simpl snd in *.

Ltac round_method :=
 match goal with
 [ H : True -> _ |- _ ] => elim H; intros; trivial; clear H
 end.
Ltac solve := myred;simpl_hyps;simpl_eq;subst;auto.



 Ltac this_not_null :=
   match goal with
   [ H : do_lvget _ 0%N = do_lvget _ 0%N,
     H1 : do_lvget _ 0%N <> Null,
     H2 : interp_value (SLvGet _ 0%N) = Null |- _] => 
     unfold interp_value in H2;
     simpl in H2;
     rewrite H in H2;
     elim (H1 H2)
   end.
   
Ltac prettyfy :=
match goal with 
[ |- interp_swp _ _ (certifiedMethod ?anno ?sig ?meth ?meth_annot) ] =>
   let x := fresh "x" in (
   let Heq := fresh "Heq" in (
   pose (x:=  (certifiedMethod anno sig meth meth_annot)); vm_compute in x;
   let res := (eval vm_compute in x) in
   assert (Heq: (certifiedMethod anno sig meth meth_annot)  = res);
   [ vm_cast_no_check (refl_equal x) | idtac];
   rewrite Heq;
   clear Heq x))
end; my_simpl. 
