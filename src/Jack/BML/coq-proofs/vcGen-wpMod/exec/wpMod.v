Require Import semantique. 
Require Import List.

(* Fixpoint  quant  (s: State )(l: list Var)(p: Prop) {struct l} : Prop :=
match l with
| nil => p
| x :: l1  =>  (quant  s l1  ( forall v ,  (s x)  = v  ->  p ) )
end. 

Definition assert_forall:  State -> list Var -> Prop  -> Prop := 
fun   (s: State) (l : list Var) (assert : Prop)  =>
        ( quant s l assert ) .
*)

Reserved Notation "'wpMod' ( a , post )  ==> pre" (at level 30).
Inductive is_wpMod : stmt_m -> Assertion -> Assertion -> Prop :=
| is_wpMod_caseSkip : forall post, wpMod(( Skip Invariant_m), post) ==> post
| is_wpMod_caseAffect :   forall post var expr, 
  wpMod((Affect  Invariant_m var expr), post)  ==>
    (update_assert post var expr ) 
| is_wpMod_caseIf : forall (post : Assertion ) (pre_t : Assertion )(pre_f : Assertion) st1 st2 bExp,    
  wpMod(st2, post) ==> pre_f  ->
    wpMod(st1, post) ==> pre_t ->
      wpMod((If  Invariant_m bExp st1 st2), post) ==>
	(fun ( s : State ) =>   
	  p_and (p_implies (p_neq ( neval s  bExp  ) 0) (pre_t s))
	   	    (p_implies (p_eq ( neval s  bExp  ) 0)     (pre_f s) ) ) 
| is_wpMod_caseWhile : forall post pre_st invariant lVar bExp S , 
   (*      (forall st,  *)
       (wpMod(S, (fun stf => p_foralls (fun st =>
            p_and
             (p_forallv (fun x => (p_implies (p_not (p_in x lVar)) (p_eq (stf ( progvar x )) (st ( progvar x ))))))
             (invariant stf)))) 
         ==> pre_st  ) -> 
      wpMod((While Invariant_m  bExp   (inv_m invariant lVar ) S ), post) ==>
         (fun st_i : State  => 
             p_and
                (* Initialement l'inv est vrai *)
                (invariant st_i )                    
            (p_and 
               (* la sortie boucle => la poste condition *)
              (p_foralls 
                  (fun st_f => 
                   p_implies
                     (p_forallv (fun x => (p_implies (p_not (p_in x lVar)) (p_eq (st_f (progvar x)) (st_i (progvar x))))))             
                       (p_implies (invariant st_f) (p_implies (p_eq (neval st_f bExp) 0) (post st_f)))))
              (* l'inv est preserve *)
              (p_foralls ( fun st_Si =>
                 (p_implies
                   (p_forallv (fun x => (p_implies (p_not (p_in x lVar)) (p_eq (st_Si (progvar x)) (st_i (progvar x))))))
          	     (p_implies (invariant st_Si) 
                          (p_implies (p_neq (neval st_Si bExp)  0) (pre_st  st_Si) ) )) ))))
	
| is_wpMod_caseSeq : forall post pre_st2 pre_st1 st1 st2 ,
      ( wpMod(st2, post) ==> pre_st2) -> 
        (wpMod(st1, pre_st2) ==> pre_st1) ->
          (wpMod(( Seq Invariant_m st1 st2 ), post) ==> pre_st1)
where "'wpMod' ( a , post )  ==> pre"  := (is_wpMod a post pre).


Lemma wpModCorrBS: 
forall ( state1: State) (stmt : stmt_m ) (state2: State) ,
       ( execBs _ state1 stmt  state2) -> 
       forall (pre post : Assertion),   ( wpMod(stmt, post) ==>  pre)  ->
         (evalMyProp ( pre state1 )) -> (evalMyProp (post state2)).
Proof with auto.
intros state1 stmt state2 Hexec; induction Hexec; intros pre post Hwp;
inversion Hwp;subst;intros;auto.
(*case skip*)
(*case assignment*)
(*case if  true*)
apply (IHHexec pre_t post);trivial.
simpl in H.
destruct H;auto.
(*case if  false*)
apply (IHHexec pre_f post);trivial.
simpl in H; destruct H;auto.
(* case while false *)
simpl in H; destruct H. destruct H0. 
apply H0; intros...

(* case while true *)
simpl in H;
destruct H. destruct H0. 
assert (h := IHHexec1 _ _ H4 (H1 s (fun var toto => refl_equal (s ( progvar var) ) )H n)).
simpl in h. 
assert(h1 := h s). 
destruct h1. 
apply (IHHexec2 _ _ Hwp).
simpl...
repeat split...
intros.
apply H0...
intros; rewrite H5...
intros.
apply H1...
intros.
rewrite  H5...
(* case seq *)
apply (IHHexec2 _ _ H1).
apply (IHHexec1 _ _ H4)...
Qed.

Fixpoint  wp_mod (S: Stmt Invariant_m) (post : Assertion) {struct S} : Assertion :=
match S with
| Skip => post
| Affect var expr => (update_assert post var expr) 
| If bExp st1 st2 => let pre_f := (wp_mod st2 post) in
                                 let pre_t := (wp_mod st1 post) in
                                 (fun (s : State ) =>   
                                 	  p_and (p_implies (p_neq ( neval s  bExp  ) 0) (pre_t s))
                                 	   	    (p_implies (p_eq ( neval s  bExp  ) 0)  (pre_f s)))
| While  bExp   (inv_m invariant lVar ) s =>
       let pre_st := (wp_mod s (fun stf => (p_foralls (fun st => 
            p_and
             (p_forallv (fun x => (p_implies (p_not (p_in x lVar)) (p_eq (stf ( progvar x) ) (st (progvar  x) )))))
             (invariant stf)))))
         in 
         (fun st_i : State  => 
             p_and
                (* Initialement l'inv est vrai *)
                (invariant st_i )                    
            (p_and 
               (* la sortie boucle => la poste condition *)
              (p_foralls 
                  (fun st_f => 
                   p_implies
                     (p_forallv (fun x => (p_implies (p_not (p_in x lVar)) (p_eq (st_f (progvar x)) (st_i (progvar x))))))             
                       (p_implies (invariant st_f) (p_implies (p_eq (neval st_f bExp) 0) (post st_f)))))
              (* l'inv est preserve *)
              (p_foralls ( fun st_Si =>
                 (p_implies
                   (p_forallv (fun x => (p_implies (p_not (p_in x lVar)) (p_eq (st_Si (progvar x)) (st_i (progvar x))))))
          	     (p_implies (invariant st_Si) 
                          (p_implies (p_neq (neval st_Si bExp)  0) (pre_st  st_Si) ) )) ))))
	
| Seq st1 st2 => 
                      let pre_st2 := wp_mod st2 post in
                      let pre_st1 := wp_mod st1 pre_st2 in
                      pre_st1
end.
Axiom triche: forall p: Prop, p.

Lemma equiv : 
forall S, forall post pre,  wp_mod S post = pre  <-> wpMod(S, post) ==> pre.
Proof with auto.
intro S. 
induction S; split; intros.

(* Skip1 *)
simpl in H; subst; apply is_wpMod_caseSkip.
(* Skip2 *)
inversion H.
simpl in |- *...

(* Affect 1 *)
simpl in H; subst.
apply  is_wpMod_caseAffect .
(* Affect 2 *)
inversion H.
simpl in |- *...

(* If 1 *)
simpl in H.
rewrite <- H.
apply is_wpMod_caseIf.
assert(h1 := IHS2 post (wp_mod S2 post)); destruct h1.
apply H0...
assert(h1 := IHS1 post (wp_mod S1 post)); destruct h1.
apply H0...

(* If 2 *)
inversion H.
simpl in |- *.
assert(h_1 := IHS1 post pre_t); destruct h_1.
assert(h1 := H8 H6).
rewrite h1.
assert(h_2 := IHS2 post pre_f); destruct h_2.
assert(h2 := H10 H5); subst...

(* While 1 *)
rewrite <- H.
cbv iota delta [wp_mod] beta iota.
(* cbv beta.
cbv iota. *)
case i.
intros a l.
apply is_wpMod_caseWhile.
intros.
simpl.
cbv iota delta [wp_mod] beta iota in IHS.
case i.
simpl in IHS.
intros.
assert (h := IHS 
(fun stf : State =>
p_foralls
  (fun st : State =>
   p_and
     (p_forallv
        (fun x : Var => p_implies (p_not (p_in x l)) (p_eq (stf (progvar x)) (st (progvar x)))))
     (a stf)))
((fix wp_mod (S0 : Stmt Invariant_m) (post0 : Assertion) {struct S0} :
   Assertion :=
   match S0 with
   | Skip => post0
   | Affect var expr => update_assert post0 var expr
   | If bExp st1 st2 =>
       fun s : State =>
       p_and (p_implies (p_neq (neval s bExp) 0) (wp_mod st1 post0 s))
         (p_implies (p_eq (neval s bExp) 0) (wp_mod st2 post0 s))
   | While bExp i0 s =>
       match i0 with
       | inv_m invariant lVar =>
           fun st_i : State =>
           p_and (invariant st_i)
             (p_and
                (p_foralls
                   (fun st_f : State =>
                    p_implies
                      (p_forallv
                         (fun x : Var =>
                          p_implies (p_not (p_in x lVar))
                            (p_eq (st_f (progvar x)) (st_i (progvar x)))))
                      (p_implies (invariant st_f)
                         (p_implies (p_eq (neval st_f bExp) 0) (post0 st_f)))))
                (p_foralls
                   (fun st_Si : State =>
                    p_implies
                      (p_forallv
                         (fun x : Var =>
                          p_implies (p_not (p_in x lVar))
                            (p_eq (st_Si (progvar x)) (st_i (progvar x)))))
                      (p_implies (invariant st_Si)
                         (p_implies (p_neq (neval st_Si bExp) 0)
                            (wp_mod s
                               (fun stf : State =>
                                p_foralls
                                  (fun st : State =>
                                   p_and
                                     (p_forallv
                                        (fun x : Var =>
                                         p_implies (p_not (p_in x lVar))
                                           (p_eq (stf (progvar x)) (st (progvar x)))))
                                     (invariant stf))) st_Si))))))
       end
   | Seq st1 st2 => wp_mod st1 (wp_mod st2 post0)
   end) S
  (fun stf : State =>
   p_foralls
     (fun st : State =>
      p_and
        (p_forallv
           (fun x : Var => p_implies (p_not (p_in x l)) (p_eq (stf (progvar x)) (st (progvar x)))))
        (a stf))))).


destruct h.
intros.
apply H0.
cbv delta [wp_mod].
simpl in  |- *...

(* While 2 *)
inversion H.
simpl.

assert(h := IHS (fun stf : State =>
     p_foralls
       (fun st : State =>
        p_and
          (p_forallv
             (fun x : Var =>
              p_implies (p_not (p_in x lVar)) (p_eq (stf  (progvar x) ) (st (progvar x)))))
          (invariant stf))) pre_st).
destruct h.
assert(h1 := H7 H5).
rewrite h1...

(* Seq 1 *)
simpl in H.
apply is_wpMod_caseSeq with (wp_mod S2 post).
assert(h1 := IHS2 post (wp_mod S2 post)); destruct h1.
apply H0...
assert(h1 := IHS1  (wp_mod S2 post) pre); destruct h1.
apply H0...

(* Seq 2 *)
inversion H.
simpl in |- *.
assert(h_1 := IHS1 pre_st2  pre); destruct h_1.
assert(h1 := H7 H5).
assert(h_2 := IHS2 post pre_st2); destruct h_2.
assert(h2:= H9 H2).
rewrite h2; rewrite h1...
Qed.