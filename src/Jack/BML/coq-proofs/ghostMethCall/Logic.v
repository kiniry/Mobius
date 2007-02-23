(*Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Require Import BasicDef. *)
Require Import Language.
Require Import Semantic.
Require Import Coq.Lists.List.
Export Language.
Export Semantic.

(*LOGIC IN A SP STYLE WITH EXPLICITE CONSEQUENCE RULE *)
Open Scope Z_scope.

Definition assertion := state -> state -> Prop.


Inductive methSpec  : methodNames -> assertion -> Type := 
   | spec : forall  (name :  methodNames ) (ass : assertion ),  methSpec name ass. 

Inductive CTX : Type :=
    | nil : CTX
    | cons :  forall (n : methodNames ) (body: stmt) (  ass : assertion) ,  CTX -> CTX .
 
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
Axiom inHeadOrTail : forall (ctx : CTX)  n b a hn hb ha tail , 
ctx = cons hn hb ha tail -> 
       ( inList  ctx n b a ) ->
              ( hn = n /\ hb = b /\  ha = a ) \/    ( inList  tail n b a )  .

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

 | WhileRule : forall  ctx  (st : stmt ) ( post post1  : assertion) e ( inv : assertion) ,
     (forall s1 s2, post1 s1 s2  /\   eval_expr s2 e = 0-> post s1 s2 ) ->
     ( forall s p t ,   eval_expr s e <>  0 -> inv s p -> post1 p t -> post1 s t ) -> 
     (forall s , eval_expr s e = 0  -> post1 s s   ) ->
     RULE ctx st  inv  ->
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


Lemma auxCall : 
forall (s1 s2: state) (post : assertion) (st : Language.stmt), 
(
(forall (t1 t2 : state) (n : methodNames) ,
           exec_stmt t1 (Call n st) t2 -> post t1 t2) -> post s1 s2 )  ->  
exec_stmt s1 st s2 -> post s1 s2. 
Proof.
intros s1 s2 post st. induction st.
intros exec ass.
apply ass.
intros.

Qed.

(*PROOF OF SOUNDNESS OF THE ABOVE RULE W.R.T. THE
 OPERATIONAL SEMANTICS GIVEN IN   Semantic.v. THE PROOF IS BY INDUCTION
 OVER THE OPERATIONAL SEMANTICS*)
 Lemma correct: forall (s: stmt) (s1 s2 : state ), (  exec_stmt  s1 s s2)  -> 
forall ctx  ( post : assertion),   RULE ctx s post   ->  
(forall t1 t2 n b ( a : assertion) , ( inList  ctx n b a  ) -> exec_stmt t1 (Call n b) t2 -> a t1 t2 )  -> post s1 s2.

Proof. 
intros st   s1 s2 exec. induction exec; simpl;auto. intros ctx post rule context.
(* ASSIGN *)
inversion rule.
apply (H3 s (update s x (eval_expr s e))).
trivial.

(* IF *) 
intros ctx post rule context.
inversion rule.
apply  ( H4  s1 s2).
split.
intros.
apply ( IHexec  ctx post1).
simpl.
apply H6.
assumption.
intros.
elim H.
assumption.

intros ctx post rule context.
inversion rule.
apply  ( H4 s1 s2).
split.
intros.
elim H8.
assumption.
intros.
apply ( IHexec ctx post2).
simpl.
apply H7.
assumption.

(*WHILE*)
(* iteration case, condition holds *)
 intros ctx post rule context.
inversion rule.
apply (H2 s1 s3).
assert (H100 := IHexec2 ctx (fun s1 s2 => post1 s1 s2 /\ eval_expr s2 e = 0 ) ).
assert ( RULE ctx (While e stmt)  (fun s1 s2 => post1 s1 s2 /\ eval_expr s2 e = 0 ) ).
apply ( WhileRule ctx stmt  (fun s1 s2 => post1 s1 s2 /\ eval_expr s2 e = 0 )  post1 e inv ).


intros.
assumption.
assumption.
assumption.
assumption.
assert (H102 := H100 H8).
simpl in *.
destruct H102.
assumption.
split.
apply ( H3 s1 s2 s3).
assumption.
apply (IHexec1 ctx inv H7).
assumption.
assumption.
assumption.

(*  condition is false *)
intros ctx post rule context.
inversion rule.
apply (H2 s1 s1).
split.
apply (H5 s1).
assumption.
assumption.

(* SEQUENCE *)
intros ctx post rule context.
inversion rule.
apply (H1 s1 s3).
exists s2.
split.
apply (IHexec1 ctx post1 H3).
assumption.
apply (IHexec2 ctx post2 H5).
assumption.

(* SKIP *)
intros ctx post rule context.
inversion rule.
apply (H s s).
trivial.


(* PROCEDURE CALL *)
intros ctx  post  rule ctxass.
inversion rule.
subst; eauto; simpl.

apply (H2 s1 s2).

assert ( H110 := IHexec (cons mName stmt post1 ctx)   post1 H4).

apply ( IHexec (cons mName stmt post1 ctx)   post1 H4).
intros.
assert ( H01 := inHeadOrTail  (cons mName stmt post1 ctx) n b a  mName stmt post1 ctx ).
assert ( mName = n /\ stmt = b /\ post1 = a \/ inList ctx n b a  ).
apply H01.
trivial.
assumption.
clear H01.
elim H1. 
clear H1.
intros H01.

destruct H01 as  (l ,   r ).
destruct r as (r1, r2).
rewrite <- r2 .
apply ( IHexec (cons mName stmt post1 ctx)   post1 H4).


(*The case when the assertion belongs to the context*)
Focus 2.
inversion rule.
subst; eauto; simpl.
intros.
apply (H2 s1 s2 ).
assert (HH := H s1 s2 mName stmt post1 H4).
apply HH.
apply (ExecCall s1 s2 stmt mName).
assumption.

Qed. 
 