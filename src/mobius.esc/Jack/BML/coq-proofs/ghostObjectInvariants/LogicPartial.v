Require Import Language.
Require Import Semantic.
Require Import Coq.Logic.Classical_Prop.
Export Language.
Export Semantic.

(*LOGIC IN A SP STYLE WITH EXPLICITE CONSEQUENCE RULE *)
Open Scope Z_scope.




 
(*RULES FOR REASONING OVER PROGRAMS AND ASSERTIONS. THIS ASSERTIONS MUST HOLD IN 
  THE TERMINAL STATE  OF THE STATEMENT EXECUTION. THUS, THIS LOGIC RULES EXPRESS PARTIAL 
  CORRECTNESS. METHODS ARE PROVIDED WITH SPECIFICATIONS WHICH STATE
   WHAT MUST HOLD IN THE TERMINAL STATE OF A METHOD. THE SPECIFICATIONS ARE GIVEN 
   BY THE MAPPING FROM METHOD NAMES TO ASSERTIONS. 
  THE CONSEQUENCE RULE IS IMPLICITE AS IT IS INLINED IN EVERY RULE*)
Inductive RULET (MS : methPost) (MPre : methPre) :  assertion -> stmt -> assertion -> Prop :=
 
 |  AffectRule : forall   x e  (pre pre1 post1 post : assertion)  , 
    (*implicite consequence rule*)
    (forall  p s, pre p s   -> pre1 p s  ) -> 
    (forall  p s, post1 p s   -> post p s  ) -> 
    (forall p ( s1 s2: state)   , 
         pre1 p s1 /\  s2 = update s1 x (eval_expr s1  e)   -> post1 p s2)  ->
    RULET MS MPre  pre  (Affect x e) post 
 
 | IfRule : forall   e (stmtT stmtF: stmt ) (pre pre1 pre2: assertion)
               (post1 post2  post: assertion) , 
    (forall p s, pre p s -> pre1 p s) -> 
    (forall p s, pre p s -> pre2 p s) ->
    (forall p s , post1 p s -> post p s) ->
    (forall p s , post2 p s -> post p s) ->
    (forall p,
     RULET MS MPre (fun s1 s2 => pre1 p s2 /\ (eval_expr s2  e) <>0)  stmtT (fun s1 s2 =>  post1 p s2)) ->
    (forall p,
     RULET MS MPre (fun s1 s2 => pre2 p s2 /\ (eval_expr s2  e) = 0)  stmtF (fun s1 s2 =>  post2 p s2) )->
    RULET MS MPre  pre  (If e stmtT stmtF)  post

 |  WhileRule : forall   e (st : stmt) (pre pre1 li post1 post : assertion),
    (forall p s, pre p s -> pre1 p s) -> 
    (forall p s , post1 p s -> post p s) ->
    (*the real while rule*)
    (forall p s, pre1 p s -> li p s) -> 
    (forall p s , li p s /\ (eval_expr s  e) = 0 -> post1 p s ) ->
    (forall p,
     RULET MS MPre (fun s1 s2 => li p s2 /\ (eval_expr s2  e) <> 0 ) st  (fun s1 s2 => li p s2)) ->
   
    RULET MS MPre pre   (While e st) post 

 |  SeqRule: forall  (stmt1 stmt2: stmt)(pre pre1 inter post1 post : assertion) , 
    (forall  p s, pre p s   -> pre1 p s  ) -> 
    (forall  p s, post1 p s   -> post p s  ) ->                             
    (forall p,  
     RULET MS MPre  (fun  s1 s2 => pre1 p s2) stmt1 (fun s1 s2 => inter p s2) ) -> 
    (forall p, 
     RULET MS MPre  (fun s1 s2 => inter p s2) stmt2 (fun s1 s2 => post1 p s2) )  -> 
    (*forall p s,  inter1 p  s -> inter2 p s -> *) 
    RULET MS MPre  pre  (Sseq stmt1 stmt2) post

 | SkipRule:   forall ( pre pre1 post1 post: assertion) ,
   (forall  p s, pre p s   -> pre1 p s  ) -> 
   (forall  p s, post1 p s -> post p s  ) ->           
   (forall p s1 s2 : state , pre p s1 -> s1 = s2 -> post p s2 ) ->
   RULET MS MPre   pre  Skip  post

 | CallRule : forall   ( mName : methodNames )  (pre  post   : assertion )  , 
   (forall p s,   pre p s  -> ( MPre mName ) s   ) ->
   (forall p s1 s2, pre p s1 ->  ( MS mName ) s1 s2  -> post p s2  ) ->
   RULET MS MPre   pre (Call mName ) post. 




 Lemma correctAux: forall MS MPre stmt   (B : body) ( P : program) , 
 (forall st (N : methodNames) (mpre: assertion1)(mpost : assertion),  
                                    (In N P) ->
                                    mpre = MPre N ->
                                    mpost = MS N -> st = B N -> RULET MS MPre (fun s1 s2 => mpre s1) st mpost )  -> 
forall (s1 s2 : state),  (  t_exec  P B s1 stmt  s2) ->
  forall (Pre : assertion) (Post: assertion) p,   Pre p s1 ->
 ( RULET MS MPre Pre stmt Post )  ->
Post p s2.
Proof.
intros MS MPre stmt B P METHS s1 s2 exec; induction exec;  simpl; subst;auto.
(*ASSIGN*)
intros pre post p  Pre rule.
inversion rule.
simpl;subst;auto.
apply H3.
apply (H5 p s ( update s x (eval_expr s e))).
split.
simpl;auto.
trivial.

(*IF*)
intros pre post p Pre rule.
inversion rule.
simpl; subst;auto.
apply (H5 p s2).

assert (ST1 := IHexec
   (fun s1 s2 : state => pre1 p s2 /\ eval_expr s2 e <> 0) 
   (fun _ s2 : state => post1 p s2) 
   p
).
simpl in ST1.
assert ( PRE1 := H3 _ _ Pre).
assert (ST11 := ST1 (conj PRE1 H) (H9 p)).
assumption.


intros pre post p Pre rule.
inversion rule.
simpl; subst;auto.
apply (H7 p s2).

assert (ST1 := IHexec
   (fun s1 s2 : state => pre2 p s2 /\ eval_expr s2 e = 0) 
   (fun _ s2 : state => post2 p s2) 
   p
).
simpl in ST1.
assert ( PRE1 := H4 _ _ Pre).
assert (ST11 := ST1 (conj PRE1 H) (H10 p)).
assumption.



(*WHILE*)

intros pre post p Pre rule.
inversion rule.
simpl; subst;auto.

apply H3.
apply H6.
assert (ST := 
IHexec1  (fun _ s2 : state => li p s2 /\ eval_expr s2 e <> 0)
 (fun _ s2 : state => li p s2) p).
simpl in ST.

assert (LI := H4 p s1 (H2 p s1 Pre)).
assert (ST1 := ST (conj LI H) (H8 p)).

assert (STW := IHexec2   (fun _ s2 : state => li p s2)
 (fun s1 s2 => li p s2 /\ eval_expr s2 e = 0) p ST1).
simpl in STW.
assert( RULET MS MPre (fun _ s2 : state => li p s2) (While e stmt)
           (fun _ s2 : state => li p s2 /\ eval_expr s2 e = 0) ).
apply ( WhileRule MS MPre e stmt 
  (fun _ s2 : state => li p s2 )
 (fun _ s2 : state => li p s2 )(fun _ s2 : state => li p s2 )
   (fun _ s2 : state => li p s2 /\ eval_expr s2 e = 0) (fun _ s2 : state => li p s2 /\ eval_expr s2 e = 0)).

trivial.
trivial.
trivial.
trivial.
intros.
apply (H8 p).


assert (STWW := STW H0).
assumption.

intros.
inversion H1.
simpl;subst;auto.
apply H5.
apply H8.
split.
apply H6.
apply H4.
assumption.
assumption.
(*SEQ*)

intros pre post p Pre rule.
inversion rule.
simpl; subst;auto.

apply H2.
apply (IHexec2 (fun _ s2 : state => inter p s2)  (fun _ s2 : state => post1 p s2) p).
apply (IHexec1 (fun _ s2 : state => pre1 p s2)  (fun _ s2 : state => inter p s2) p).
apply H1.
assumption.
apply (H4 p).
apply (H6 p).

(*SKIP*)
intros;simpl;auto.
inversion H0.
simpl;subst;auto.
apply (H3 p s s).
assumption.
trivial.

(*CALL*)
intros pre post p Pre rule.
inversion rule.
simpl;subst;auto.
apply (H3 p s1 s2).
assumption.
apply (IHexec  (fun s1 s2 => ( MPre mName) s1) ( MS mName  )  ).
apply (H1 p s1).
assumption.
apply ( METHS (B mName)  mName (MPre mName) (MS mName)).
assumption.
trivial.
trivial.
trivial.
Qed.


Lemma conseqRule : forall stmt MS MPre  (pre1 pre2 post1 post2 : assertion), 
(forall p s, pre1  p s -> pre2 p s) ->
(forall p s, post2  p s -> post1 p s) ->
(RULET MS MPre pre2 stmt post2 ) ->
(RULET MS MPre pre1 stmt post1).
Proof.
intros stmt; induction stmt; intros MS MPre pre1 pre2 post1 post2 sidePre sidePost rule2; inversion rule2;
 simpl;subst;auto.
(*ASSIGN*)
apply (AffectRule MS MPre v e pre1  pre2 post2 post1).
assumption.
assumption.
intros.
apply H3.
apply (H5 p s1 s2).
destruct H as (H11, H12).
split.
apply H1.
assumption.
assumption.

(*IF *)
apply (IfRule MS MPre e stmt1 stmt2 pre1  pre0 pre3  post0 post3 post1).

intros.
apply H2.
apply sidePre.
assumption.

intros.
apply H3.
apply sidePre.
assumption.

intros.
apply sidePost.
apply H4.
assumption.

intros.
apply sidePost.
apply H6.
assumption.

assumption.
assumption.

(*WHILE*) 
apply (WhileRule MS MPre e stmt pre1 pre0 li post0 post1).

intros.
apply H1.
apply sidePre.
assumption.

intros.
apply sidePost.
apply H2.
assumption.
assumption.
assumption.
assumption.

(*SEQ*)
apply (SeqRule MS MPre stmt1 stmt2 pre1  pre0 inter post0 post1 ).

simpl;subst;auto.
simpl;subst;auto.
assumption.
assumption.

(*SKIP*)
apply (SkipRule MS MPre pre1 pre0 post0 post1 ).
simpl;subst;auto.
simpl;subst;auto. 
intros.
apply sidePost.
apply (H1 p s1 s2).

simpl;subst;auto. 
assumption.

(*CALL*)
apply (CallRule MS MPre m pre1 post1).

intros.
apply (H0 p s).
apply sidePre.
assumption.

intros.
apply sidePost.
apply (H2 p s1 s2).
apply sidePre.
assumption.
assumption.
Qed.
