Require Import semantique. 
Require Import List.
Fixpoint  quant  (s: State )(l: list Var)(p: Prop) {struct l} : Prop :=
match l with
| nil => p
| x :: l1  =>  (quant  s l1  ( forall v ,  (s x)  = v  ->  p ) )
end. 

Definition assert_forall:  State -> list Var -> Prop  -> Prop := 
fun   (s: State) (l : list Var) (assert : Prop)  =>
        ( quant s l assert ) .

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
| is_wpMod_caseWhile : forall post pre_st invariant lVar bExp st1 , 
      (forall St, 
       (wpMod(st1, (fun sti => p_and
         (p_forallv (fun x => (p_implies (p_not (p_in x lVar)) (p_eq (sti x) (St x)))))
           (invariant sti))) ==> pre_st) -> 
           wpMod((While   Invariant_m  bExp   (inv_m invariant lVar ) st1 ),
                         post) ==>
             (fun st_i : State  =>  p_and
              (p_forallv (fun x => (p_implies (p_not (p_in x lVar)) (p_eq (st_i x) (St x)))))
                 (p_and
                   (invariant st_i ) (* Initialement l'inv est vrai *)
                  
                 (* la sortie boucle => la poste condition *)
                 (p_and ( p_foralls 
                      (fun st_fin => p_implies
                       (p_forallv (fun x => (p_implies (p_not (p_in x lVar)) (p_eq (st_i x) (St x)))))             
                       (p_implies (invariant st_fin) (p_implies (p_eq (neval st_fin bExp) 0) (post st_fin)))))
                 
                 (p_foralls ( fun st_ =>
                   (* l'inv est preserve *) (p_implies
                   (p_forallv (fun x => (p_implies (p_not (p_in x lVar)) (p_eq (st_i x) (St x)))))
          	     (p_implies (invariant st_) 
                          (p_implies (p_neq (neval st_ bExp)  0) (pre_st  st_) ) )) ))))))
	
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
simpl in H; destruct H. destruct H0.  destruct H1.
apply (H1 s);auto.
(* case while true *)
simpl in H;
destruct H. destruct H0. destruct H1.
assert (H6 := H2  s H H0 n).
assert (H7 := IHHexec1 _ _ H4 H6).
apply (IHHexec2 _ _ Hwp).
simpl in H7; destruct H7.
simpl in |- *; repeat split...
(* case seq *)
apply (IHHexec2 _ _ H1).
apply (IHHexec1 _ _ H4)...
Qed.



   
