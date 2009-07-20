Require Import semantiqueAux1. 
Require Import List.

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
	  (( neval s  bExp  ) <> 0 ->  pre_t s)
	    /\ 
	    ( ( neval s  bExp  ) = 0  ->   pre_f s ) ) 
| is_wpMod_caseWhile : forall post pre_st invariant lVar bExp st1 , 
      (forall St  ,
       (wpMod(st1, (fun sti =>  (forall x, ~In x lVar -> sti x = St x) /\ invariant sti)) ==> pre_st) 
         -> 
           wpMod((While   Invariant_m  bExp   (inv_m invariant lVar ) st1 ),  post ) ==>
               ( fun st_i : State  =>  
               ( forall x, ~In x lVar -> st_i x = St x ) 
                /\   
                (invariant st_i ) (* Initialement l'inv est vrai *)
                /\ 
                (* la sortie boucle => la poste condition *)
                (  forall st_fin : State, 
                   (forall  x: Var,   ~In x  lVar  -> st_fin x  = St x) -> 
                      invariant st_fin -> neval st_fin bExp  = 0  ->  post st_fin) 
                 /\ 
                ( forall st_ : State, 
                   (* l'inv est preserve *)
                   ( (forall  x: Var,   ~In x  lVar  -> st_i x  = St x) -> 
          	     invariant st_ -> neval st_ bExp  <> 0 -> pre_st  st_ ) )) )
	
| is_wpMod_caseSeq : forall post pre_st2 pre_st1 st1 st2 ,
      ( wpMod(st2, post) ==> pre_st2) -> 
        (wpMod(st1, pre_st2) ==> pre_st1) ->
          (wpMod(( Seq Invariant_m st1 st2 ), post) ==> pre_st1)
where "'wpMod' ( a , post )  ==> pre"  := (is_wpMod a post pre).


Lemma wpModCorrBS: 
forall ( state1: State) (stmt : stmt_m ) (state2: State) ,
       ( execBs _ state1 stmt  state2) -> 
       forall (pre post : Assertion),   ( wpMod(stmt, post) ==>  pre)  ->
         ( pre state1 ) -> (post state2).
Proof with auto.
intros state1 stmt state2 Hexec; induction Hexec; intros pre post Hwp;
inversion Hwp; subst; intros; auto.
(*case skip*)
(*case assignment*)
(*case if  true*)
apply (IHHexec pre_t post);trivial.
destruct H0;auto.
(*case if  false*)
apply (IHHexec pre_f post);trivial.
destruct H0;auto.
(* case while false *)
destruct H0. destruct H1.  destruct H2.
apply (H2 s);auto.
(* case while true *)
destruct H0. destruct H1. destruct H2.
assert (H6 := H3  s H0 H1 H).
assert (H7 := IHHexec1 _ _ H5 H6).
apply (IHHexec2 _ _ Hwp).
destruct H7.
repeat split...
(* case seq *)
apply (IHHexec2 _ _ H1).
apply (IHHexec1 _ _ H4)...
Qed.



   
