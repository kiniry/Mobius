
Require Import Language.
Require Import SemanticLevels.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Export Language.
Export  SemanticLevels.

(*LOGIC IN A SP STYLE WITH EXPLICITE CONSEQUENCE RULE *)
Open Scope Z_scope.

Definition assertion := state -> state -> Prop.


Inductive methSpec  : methodNames -> assertion -> Type := 
   | spec : forall  (name :  methodNames ) (ass : assertion ),  methSpec name ass. 

Inductive CTX : Type :=
    | nil : CTX
    | cons :   methodNames -> stmt ->  assertion -> CTX -> CTX .
 
Fixpoint  inList (ctx: CTX ) ( name2 :  methodNames  ) (body2 :stmt)( ass2 : assertion ){struct ctx } : Prop  :=
   match ctx with 
   | nil =>  False
   | cons name1 body1 ass1    l =>         
       ( name1 = name2 /\ body1 = body2 /\  ass1 = ass2 ) \/    ( inList l name2 body2 ass2) 
 
end. 

(* Fixpoint  getSpec (ctx: CTX ) ( name :  methodNames  ){struct ctx } :  gstmt * assertion     :=
   match ctx with 
   | nil =>  (Skip  , fun s1 s2 => False )
   | cons name1 body1 ass1    l =>  match  name1 with   
                                                             | name =>  (body1 , ass1) 
                                                             |  _  =>  
                                                             getSpec  l  name 
                                                             end
end. 
*)



(*RULES FOR REASONING OVER PROGRAMS AND ASSERTIONS.  
THE CONSEQUENCE RULE IS IMPLICITE AS IT IS INLINED IN EVERY RULE*)
Inductive RULE: CTX -> stmt -> assertion -> Prop :=
 
 | AffectRule : forall  ctx x e (post : assertion) , 
     (forall  (s1 s2: state),   s2 = update s1 x (eval_expr s1 e)   -> post s1 s2)  ->
     RULE  ctx (Affect x e) post
 
 | IfRule : forall ctx  e (stmtT stmtF: stmt ) ( post1  post2 post : assertion) , 
    ( forall ( s1 s2: state),  ( (not (eval_expr s1 e = 0)) -> post1 s1 s2) /\ 
                                          (eval_expr s1 e = 0 ->  post2 s1 s2)  -> post s1 s2) ->
    RULE ctx stmtT   post1   ->
    RULE ctx stmtF   post2   ->
    RULE ctx (If e stmtT stmtF) post 

 | WhileRule : forall  ctx  (st : stmt ) ( post post1  : assertion) e (* inv : assertion *) ,
     (forall s1 s2, post1 s1 s2  /\   eval_expr s2 e = 0-> post s1 s2 ) ->
     ( forall s p t ,   eval_expr s e <>  0 -> post1 s p -> post1 p t -> post1 s t ) -> 
     (forall s , eval_expr s e = 0  -> post1 s s   ) ->
     RULE ctx st  post1 ->
     RULE ctx (While e st) post  

 |  SeqRule: forall ctx (stmt1 stmt2: stmt ) ( post1  post2  post: assertion), 
   ( forall s1 s2,  (exists p , post1   s1 p /\   post2  p s2) -> post s1 s2    ) -> 
   RULE  ctx stmt1  post1 ->
   RULE  ctx stmt2 post2   ->
   RULE  ctx (Sseq stmt1 stmt2) post

 | SkipRule:   forall   ctx (post: assertion),
   ( forall  (s1 s2: state ) ,  s1 = s2 -> post s1 s2) ->
   RULE  ctx Skip  post
 
 | CallRule : forall  ctx (body : stmt )  ( mName : methodNames ) ( post  post1 : assertion ) , 
   (forall (s1 s2 : state ), post1 s1 s2 -> post s1 s2 ) ->
   RULE (cons mName body post1    ctx   ) body  post1 ->
   RULE ctx (Call mName body)  post
 
 | CallRuleCtx : forall ctx  (body : stmt ) ( mName : methodNames ) ( post  post1 : assertion ) , 
      (forall (s1 s2 : state ), post1 s1 s2 -> post s1 s2 ) ->
      ( inList ctx   mName body post1 ) ->
      RULE ctx  (Call mName body)  post.


Lemma  mplus2eqmplus1plus1: forall n0 n, (n0+2)%nat = S n -> (n0 + 1)%nat = n.
Proof.
intros.
omega.
Qed.

Lemma whileAux: 
forall n s1 s2 (post : assertion)  st e,  exec_stmtN n s1 (While e  st) s2 -> 
   (forall s : state, eval_expr s e = 0 -> post s s ) -> 
   
   (forall s p t : state,
              eval_expr s e <> 0 -> post s p -> post p t -> post s t ) ->
   (forall s1 s2 : state, exec_stmtN n s1 st s2 -> post s1 s2 ) -> 
 (  post s1 s2  /\ eval_expr s2 e = 0 ) .
Proof.

intros n. induction n. 

(* base case : n =0 *)
 intros s1 s2 post  st e exW.
intros.
assert ( contrad := levelgt0  (While e  st)  s1 s2  exW ) .
elim contrad.

(* inductive case*)
intros.
inversion H.
simpl;subst;auto.
assert (A := mplus2eqmplus1plus1 n0 n H3).
rewrite A in H8.
rewrite A in H10.


assert (H1000 := IHn s3 s2 post st e H10 H0 H1).
assert (forall s1 s2 : state, exec_stmtN n s1 st s2 -> post s1 s2). 
apply ( forSmallerAlso1 n (S n) st post).
omega.
assumption.

assert (H1001 := H1000 H4).
destruct H1001. 

split.
apply ( H1 s1 s3 s2 ).
assumption.
apply ( H2 s1 s3).
apply (monot  n st s1 s3   H8).
omega.
assumption.
assumption.
simpl;subst;auto.
Qed.


(* SIMPLE VERSION OF AUXILIARY LEMMA FOR PROCEDURE CALLS WHICH PROCEEDS BY INDUCION 
OVER THE CALL DEPTH N. IT IS USED IN THE PROOF OF SOUNDNESS IN THE CASE
OF A METHOD CALL*)
Lemma callAux : forall  M  mName body (post: assertion) ,
(forall n : nat,
         (forall (t1 t2 : state) ,
          exec_stmtN n t1 (Call mName body) t2 -> post t1 t2) ->
         forall s1 s2 : state, exec_stmtN n s1 body s2 -> post s1 s2 ) -> 

  forall s1 s2 , 
     exec_stmtN M s1 (Call mName body) s2 ->  post s1 s2. 
Proof.
intros n. induction n.
(* base case : n =0 *)
intros  mName body post   ass  s1 s2  exW  .
assert ( contrad := levelgt0  (Call mName body)  s1 s2  exW ) .
elim contrad.


(* induction case *)
intros mName body post   ass  s1 s2 exec.
assert (IH1 := IHn mName body post ass).
assert ( IH3 := ass n IH1).
inversion exec.
simpl;subst;auto.
assert ( (n0 + 1)%nat = n ).
omega.
rewrite H0 in H4.
clear H0 H.
apply IH3.
assumption.
Qed.  

Lemma constructCtx : forall n ctx mName body ( post : assertion ),
( forall (t1 t2 : state) (b : stmt) (a : assertion) (mName : methodNames),
    inList ctx mName b a -> exec_stmtN n t1 (Call mName b) t2 -> a t1 t2 ) ->
(forall s1 s2 ,  exec_stmtN n s1 (Call mName body) s2 -> post s1 s2 ) -> 

 (forall (t1 t2 : state) (b : stmt) (a : assertion) (mName0 : methodNames),
       inList (cons mName body post ctx) mName0 b a ->
       exec_stmtN n t1 (Call mName0 b) t2 -> a t1 t2).
Proof.
intros.
elim H1.
intros.
destruct H3 as ( name, ( bodies, posts)).
rewrite <- bodies in H2.
rewrite <- posts .
rewrite <- name in H2.
apply H0.
assumption.
intros.
apply ( H t1 t2 b a mName0).
assumption.
assumption.
Qed.


Lemma callAux1 : forall  M  ctx mName body (post: assertion) ,

(forall n : nat,
         (forall (t1 t2 : state) (b : stmt) (a : assertion)
            (mName0 : methodNames),
          inList (cons mName body post ctx) mName0 b a ->
          exec_stmtN n t1 (Call mName0 b) t2 -> a t1 t2) ->
         forall s1 s2 : state, exec_stmtN n s1 body s2 -> post s1 s2) -> 



  forall s1 s2 ,  (forall (t1 t2 : state) (b : stmt) (a : assertion) (mName : methodNames),
      inList ctx mName b a -> exec_stmtN M t1 (Call mName b) t2 -> a t1 t2) ->
     exec_stmtN M s1 (Call mName body) s2 ->  post s1 s2. 
Proof.
intros n. induction n.
(* base case : n =0 *)
intros ctx mName body post   ass  s1 s2 ass1  exW  .
assert ( contrad := levelgt0  (Call mName body)  s1 s2  exW ) .
elim contrad.


(* induction case *)
intros ctx mName body post   ass  s1 s2 ass1 exec.
assert (IH1 := IHn ctx mName body post ass).
assert ( 
forall (t1 t2 : state) (b : stmt) (a : assertion)
         (mName : methodNames),
       inList ctx mName b a ->
       exec_stmtN n t1 (Call mName b) t2 -> a t1 t2
).
intros.
apply (ass1 t1 t2 b a mName0 ).
assumption.
apply (  monot n  (Call mName0 b)  t1 t2  H0 ).
omega.
assert ( forall s1 s2, exec_stmtN n s1 (Call mName body) s2 -> post s1 s2).
intros.
apply (  IH1 s0 s3 H H0).
assert ( CtxInc := constructCtx  n ctx mName body post H H0).
assert ( IH3 := ass  n  CtxInc).
inversion exec.
simpl;subst;auto.
assert ( (n0 + 1)%nat = n ).
omega.
rewrite H2 in H6.
apply IH3.
assumption.
Qed.  


(*PROOF OF SOUNDNESS OF THE ABOVE RULE W.R.T. THE
 OPERATIONAL SEMANTICS GIVEN IN   Semantic.v. THE PROOF IS BY INDUCTION
 OVER THE OPERATIONAL SEMANTICS*)
 Lemma correct: forall  (s: stmt)  ctx  ( post : assertion),   RULE ctx s post   ->  
forall n, 
(forall t1 t2  b ( a : assertion)  (mName : methodNames ), ( inList  ctx mName b a  ) ->  
                           exec_stmtN n t1 (Call mName b) t2 -> a t1 t2 ) ->
   forall  (s1 s2 : state ),  exec_stmtN  n s1 s s2 -> post s1 s2.

Proof. 
intros  st    ctx post rule;
induction rule; intros n ass s1 s2 exec ; simpl;subst;auto.

(* ASSIGN *)
apply H.
inversion exec.
trivial.

(* IF *) 
inversion exec.
simpl;subst;auto.
apply (H s1 s2).
split.
intros.
eapply ( IHrule1 (n0 + 1)%nat ). 
assumption.
assumption.
intros.
elim H6.
assumption.
simpl;subst;auto.
apply (H s1 s2).
split.
intros.
elim H0.
assumption.
intros.
eapply ( IHrule2 (n0 + 1)%nat ) .  
assumption.
assumption.

(*WHILE*)
(* iteration case, condition holds *)
apply H.
inversion exec.
simpl;subst;auto.
assert (execNplus2 := monot  ( n0 +1)%nat st s1 s3  H7 (n0 +2)%nat ).
assert (execAtnplus2: exec_stmtN (n0 + 2) s1 st s3).
apply execNplus2.
omega.
clear execNplus2.

assert (IH1 := IHrule (n0+2)%nat ass  s1 s3  execAtnplus2).
assert (theDiff:= whileAux ( n0 + 1)   s3 s2  post1 st e H9  H1 H0).
assert (forall s1 s2 : state, exec_stmtN (n0 + 1) s1 st s2 -> post1 s1 s2).
apply (forSmallerAlso1 (n0 + 1) ( n0 +2 ) st post1  ). 
omega.
intros. apply (IHrule  (n0+2)%nat ) .
assumption.
assumption.
assert ( IH2 := theDiff H2).
clear theDiff.
split.
apply (H0 s1 s3 s2 ).
assumption.
assumption.
destruct IH2.
assumption.
destruct IH2.
assumption.

(* condition of while is false *)
simpl;subst;auto.

(* SEQUENCE *)
inversion exec.
simpl;subst;auto.
apply (H s1 s2).
exists s3.
split.
apply (IHrule1 (n0+1)%nat ass   s1 s3 H4).
apply (IHrule2 (n0+1)%nat ass  s3 s2 H6).

(* SKIP *)
inversion exec.
simpl;subst;auto. 

(* PROCEDURE CALL: INDUCTIVE CASE *)
apply H.
apply ( callAux1 n ctx  mName body post1 IHrule  s1 s2 ass exec).

(* PROCEDURE CALL*)
apply H.
apply (ass s1 s2  body post1 mName ).
assumption.
assumption.
Qed.


 