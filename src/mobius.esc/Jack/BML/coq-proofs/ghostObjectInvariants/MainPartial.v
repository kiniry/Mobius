Require Import  LogicPartial.
Require Import LogicPartialGhost.
Require Import Coq.Logic.Classical_Prop.
Require Import Language.
Require Import  Coq.Bool.Bool.
Export Logic.
Export LogicPartialGhost. 

(* THILE FILE CONTAINS A DEFINITION OF THE TRANSFORMATION FROM 
PROGRAMS WITH GHOST VARIABLES INTO PROGRAMS WHICH DO NOT TREAT GHOST.
THE FILE ALSO STATES THE MAIN LEMMA OF THIS FORMALIZATION :  
A DERIVABILITY OF A JUDGEMENT WITH GHOSTS ( PROGRAM STATEMENT 
 AND ASSERTION WITH GHOSTS )
 IN LOGIC SYSTEM FOR REASONING 
ABOUT PROGRAMS WITH GHOSTS IMPLIES DERIVABILITY OF 
THE RESPECTIVE STATTEMENT AND JUDGEMENT WITHOUT GHOST *)
Fixpoint  transform (gstmt: gStmt){struct gstmt } :stmt  :=
match gstmt with 
 | (GAffect x e ) => (Affect x e) 
 | ( GIf e gst1 gst2) =>
   let st1 := transform  gst1 in
   let st2 := transform  gst2 in 
   (If e st1 st2)
 | (GWhile e gst) => 
   let st :=  transform  gst in 
   (While e st)
 | (GSseq gst1 gst2 )  =>
   let st1 :=  transform gst1 in
   let st2 :=  transform gst2 in
   (Sseq st1 st2) 
 | GSkip  => Skip
 | ( GCall mName ) => 
    (Call mName )	
  | Pack => Skip 
  | Unpack => Skip 
end.

Definition  transformPost (GSpec: gMethPost)( I: Invariant) : methPost   :=
fun mName => ( fun s1  s2=> forall st1, exists st2, 
      (st2 = true -> I s2)  /\  (GSpec mName) s1 st1  s2 st2 ).

Definition  transformPre (GPre: gMethPre) ( I: Invariant) : methPre   :=
fun mName => ( fun s  => exists st,    
     ( (st =true -> I s) /\ ( GPre mName) s st )).
    

(*deprecated  
Definition  transformPre (GPre: gMethPre) ( I: Invariant) : methPre   :=
fun mName => ( fun s1 s2  => exists st1, exists st2,   
     ( (st2=true -> I s2) /\ ( GPre mName) s1 st1 s2 st2 )).*)
      
Definition  transformBody (gb: gBody) : body   :=
fun mName => ( transform  (gb mName )   ).
                        
(*  
Definition  transformInv (GInv: GmethInv) : methInv   :=
fun mName => ( fun s1 events s2=> forall g1, exists g2, ( GInv mName) s1 g1 events s2 g2 ).

*)



 
(* MAIN THEOREM : derivability in logic with ghosts
 implies derivability of the respective interpretation of formulas in a logic without ghosts  *)
Lemma ghostLogicImpliesStandardLogic: forall  (gst: gStmt ) 
  (Body : gBody ) (gPre  gPost  : gAssertion)   (GMPre : gMethPre) 
  (GMPost: gMethPost) ( I : Invariant ), 
 let st := transform  gst in 
 GRULET GMPost GMPre I  gPre gst gPost -> 
forall p pst,
 RULET (transformPost GMPost I)
                (transformPre  GMPre I) 
                (fun s1  s2  => forall (st1: bool), exists st2, ( st2  = true -> I s2  ) /\ gPre p pst s2 st2)
                st  
                (fun s1  s2  => forall (st1: bool), exists st2, ( st2  = true -> I s2  ) /\ gPost p pst s2 st2)
               .

Proof.
intros  gst Body gPre  Gpost  GPRE GPOST  I; simpl;subst;auto. intros grule;  induction grule.  

(**)
unfold transform . simpl;subst;auto.
intros.
 apply ( AffectRule  ( transformPost GPOST I ) ( transformPre GPRE I )  x e  
 (fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre p pst s2 st2)
 (fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre1 p pst s2 st2)
   (fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post1 p pst s2 st2)
  (fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post p pst s2 st2)

).

intros.
assert (H33 := H3 pst).
elim H33.
intros.
exists x0.
destruct H5 as (INV, PRE0).
split.
assumption.
apply H.
assumption.

intros.
assert (H33 := H3 pst). 
elim H33.
intros.
exists x0.

destruct H5 as (INV, PRE0).
split.
assumption.
apply H0.
assumption.


intros.
destruct H3 as (H31, H32).
assert  (H33 := H31 pst).
clear H31.
elim H33.
intros.
exists x0.
destruct H3 as (INV, PRE1).
split.
assert (TF := H1 _ _ _ _ PRE1).
intros.
rewrite H3 in TF.

assert ( TNF := diff_true_false).
elim TNF.
assumption. 

apply (H2 p s1 s2 pst x0 x0 ).
split.
assumption.
assumption.



(*IF*)
intros.
apply (IfRule ( transformPost GPOST I )  ( transformPre GPRE I )  
 e 
 (transform stmtT) 
 (transform stmtF) 
 (fun s1 s2 : state =>
   forall st1 : bool,
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre p pst s2 st2)
 (fun s1 s2 : state =>
   forall st1 : bool,
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre1 p pst s2 st2)
 (fun s1 s2 : state =>
   forall st1 : bool,
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre2 p pst s2 st2)
 (fun s1 s2 : state =>
   forall st1 : bool,
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post1 p pst s2 st2)
 (fun s1 s2 : state =>
   forall st1 : bool,
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post2 p pst s2 st2)
 (fun s1 s2 : state =>
   forall st1 : bool,
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post p pst s2 st2)
).

intros.
assert (H33 := H7 st1).
elim H33.
intros.
exists x.
destruct H8 as (INV, PRE0).
split.
assumption.
apply H.
assumption.

intros.
assert (H33 := H7 st1).
elim H33.
intros.
exists x.
destruct H8 as (INV, PRE0).
split.
assumption.
apply H0.
assumption.


intros.
assert (H33 := H7 st1).
elim H33.
intros.
exists x.
destruct H8 as (INV, PRE0).
split.
assumption.
apply H1.
assumption.


intros.
assert (H33 := H7 st1).
elim H33.
intros.
exists x.
destruct H8 as (INV, PRE0).
split.
assumption.
apply H2.
assumption.


assert (H41 := H4 p pst p pst).
intros.

apply (conseqRule  (transform stmtT) (transformPost GPOST I)
 (transformPre GPRE I)

(fun _ s2 : state =>
   (bool ->
    exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre1 p pst s2 st2) /\
   eval_expr s2 e <> 0) 

 (fun _ s2 : state =>
         bool ->
         exists st2 : bool,
           (st2 = true :>bool -> I s2) /\
           pre1 p pst s2 st2 /\ eval_expr s2 e <> 0) 
 (fun _ s2 : state =>
         bool ->
         exists st2 : bool, (st2 = true :>bool -> I s2) /\ post1 p pst s2 st2)
(fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post1 p pst s2 st2)

).

intros.
destruct H7 as (H71 , H72).

assert (H77 := H71 H8).
elim H77.
clear H77.
intros.
exists x.
destruct H7.
split.
assumption.
split.
assumption.
assumption.

intros.
assert (H77 := H7 H8).
elim H77.
intros.
destruct H9 as (H91, H92).
exists x.
split.
assumption.
assumption.
assumption.

intros.
apply (conseqRule  (transform stmtF)
(transformPost GPOST I) (transformPre GPRE I)
  (fun _ s2 : state =>
   (bool ->
    exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre2 p pst s2 st2) /\
   eval_expr s2 e = 0 :>value)
(fun _ s2 : state =>
        bool ->
        exists st2 : bool,
          (st2 = true :>bool -> I s2) /\
          pre2 p pst s2 st2 /\ eval_expr s2 e = 0 :>value)
 
  (fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post2 p pst s2 st2)

(fun _ s2 : state =>
        bool ->
        exists st2 : bool, (st2 = true :>bool -> I s2) /\ post2 p pst s2 st2)

).
intros.
destruct H7 as (H71, H72).
assert (H77 := H71 H8).
elim H77.
intros.
destruct H7 as (H91, H92).
exists x.
split.
assumption.
split.
assumption.
assumption.


intros.
assert (H77 := H7 H8).
elim H77.
intros.
destruct H9 as (H91, H92).
exists x.
split.
assumption.
assumption.
assert ( H66 := H6 p pst p pst).
assumption.


(*WHILE*)
intros.
apply (WhileRule  (transformPost GPOST I )  ( transformPre GPRE I )
    
   e (transform stmt) 
 (fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre p pst s2 st2)
 
(fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre1 p pst s2 st2)
 
(fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\  li p pst s2 st2)
  
 
 (fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post1 p pst s2 st2)

 (fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post p pst s2 st2)
  

). 


intros.
assert (H55 := H5 H6).
elim H55.
intros.
exists x.
destruct H7 as (H71, H72).
split.
assumption.
apply H.
assumption.

intros.
assert (H55 := H5 H6).
elim H55.
intros.
exists x.
destruct H7 as (H71, H72).
split.
assumption.
apply H0.
assumption.

intros.
assert (H55 := H5 H6).
elim H55.
intros.
exists x.
destruct H7 as (H71, H72).
split.
assumption.
apply H1.
assumption.

intros.
destruct H5 as (H51, H52).
assert (H55 := H51 H6).
elim H55.
intros.
exists x.
destruct H5 as (H71, H72).
split.
assumption.
apply H2.
split.
assumption.
assumption.

intros.
assert (H44 := H4 p pst p pst).

apply (conseqRule  (transform stmt)
(transformPost GPOST I)  (transformPre GPRE I)
  (fun _ s2 : state =>
   (bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ li p pst s2 st2) /\
   eval_expr s2 e <> 0) 
  (fun _ s2 : state =>
         bool ->
         exists st2 : bool,
           (st2 = true :>bool -> I s2) /\
           li p pst s2 st2 /\ eval_expr s2 e <> 0)
   (fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ li p pst s2 st2)
 (fun _ s2 : state =>
         bool ->
         exists st2 : bool, (st2 = true :>bool -> I s2) /\ li p pst s2 st2)
).
intros.
destruct H5 as ( H51, H52). 
assert (H55 := H51 H6).
elim H55.
intros.
exists x.
destruct H5.
split.
assumption.
split.
assumption.
assumption.

intros.

assert (H55 := H5 H6).
elim H55.
intros.
exists x.
destruct H7.
split.
assumption.
assumption.

assumption.


(*SEQ*)
intros.
apply (SeqRule (transformPost GPOST I )    ( transformPre GPRE I )
   
   (transform stmt1) (transform stmt2)
   
   (fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre p pst s2 st2)
   (fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre1 p pst s2 st2)
   (fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ inter p pst s2 st2)
   (fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post1 p pst s2 st2)
   (fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post p pst s2 st2)
).

intros.
assert (H55 := H5 H6).
elim H55.
intros.
exists x.
destruct H7.
split.
assumption.
apply H.
assumption.

intros.
assert (H55 := H5 H6).
elim H55.
intros.
exists x.
destruct H7.
split.
assumption.
apply H0.
assumption.

intros.
assert (H22 := H2 p pst p pst).
apply (conseqRule  (transform stmt1) (transformPost GPOST I) (transformPre GPRE I)

 (fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre1 p pst s2 st2)
 (fun _ s2 : state =>
         bool ->
         exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre1 p pst s2 st2)
 (fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ inter p pst s2 st2)
(fun _ s2 : state =>
         bool ->
         exists st2 : bool, (st2 = true :>bool -> I s2) /\ inter p pst s2 st2)
).
intros.
assert (H55 := H5 H6).
elim H55.
intros.
exists x.
destruct H7.
split.
assumption.
assumption.

intros.
assert (H55 := H5 H6).
elim H55.
intros.
exists x.
destruct H7.
split.
assumption.
assumption.

assumption.

intros.
apply (conseqRule  (transform stmt2) (transformPost GPOST I)
(transformPre GPRE I)

(fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ inter p pst s2 st2)
(fun _ s2 : state =>
        bool ->
        exists st2 : bool, (st2 = true :>bool -> I s2) /\ inter p pst s2 st2)
(fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post1 p pst s2 st2)
 (fun _ s2 : state =>
        bool ->
        exists st2 : bool, (st2 = true :>bool -> I s2) /\ post1 p pst s2 st2)

).
intros.
assert (H55 := H5 H6).
elim H55.
intros.
exists x.
destruct H7.
split.
assumption.
assumption.

intros.
assert (H55 := H5 H6).
elim H55.
intros.
exists x.
destruct H7.
split.
assumption.
assumption.

apply (H4 p pst p pst).

(*SKIP*)
intros.
apply (  SkipRule  (transformPost GPOST I )  ( transformPre GPRE I )
    
(fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre p pst s2 st2)
(fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre1 p pst s2 st2)
 (fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post1 p pst s2 st2)
 (fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post p pst s2 st2)
).
intros.
intros.
assert (H55 := H2 H3).
elim H55.
intros.
exists x.
destruct H4.
split.
assumption.
apply H.
assumption.

intros.
assert (H55 := H2 H3).
elim H55.
intros.
exists x.
destruct H4.
split.
assumption.
apply H0.
assumption.

intros.
assert (H55 := H2 H4).
elim H55.
intros.
exists x.
destruct H5.
split.
intros.
rewrite H3 in H5.
apply H5.
assumption.

apply (H1 p s1 s2 pst x x).
assumption.
assumption.


(*CALL*)
intros.
apply ( CallRule  (transformPost GPOST I) (transformPre GPRE I)
mName
(fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre p pst s2 st2)
 (fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post p pst s2 st2)
).


unfold transformPre.
intros.
assert (H11 := H1 true).
elim H11.
intros.
exists x.
destruct H2.
split.
assumption.
apply ( H p s pst x).
assumption.

intros.
assert (H11 := H1 H3). 
unfold transformPost in H2.
elim H11.
intros.
assert (H22 := H2 x).
elim H22.
intros.
exists x0.

destruct H4 as (IS1, PRE1).
destruct H5 as (IS2, GPOSTs1s2).
split.
assumption.

apply (H0 p s1 s2 pst x x0).
assumption.
assumption.

(*PACK*)
intros.
unfold transform.
apply (
SkipRule  (transformPost GPOST I )  ( transformPre GPRE I )
     (fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre p pst s2 st2)
 (fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre p pst s2 st2)
 (fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post p pst s2 st2)
(fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post p pst s2 st2)
).
trivial.
trivial.
intros.

elim (H2 H4).
intros.

exists true.
destruct H5.
split.
intros.
rewrite H3 in H6.
apply (H0 p s2 pst x ).
assumption.
apply (H1 p s1 s2 pst x true).
split.
assumption.
split.
assumption.
trivial.

(*UNPACK*)
intros.
unfold transform.
apply (
SkipRule  (transformPost GPOST I )  ( transformPre GPRE I )
     (fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre p pst s2 st2)
 (fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre p pst s2 st2)
 (fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post p pst s2 st2)
(fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post p pst s2 st2)
).
trivial.
trivial.

intros.
exists false.
elim (H1 H3).
intros.
destruct H4.
split.
intros.
assert (CON := diff_true_false).
destruct CON.
auto.
apply (H0 p s1 s2 pst x false).
split.
assumption.
split.


assumption.
trivial.

(*INV*)
intros.
assert (H00 := H0 p pst p pst).
apply (conseqRule  
(transform stmt)
(transformPost GPOST I)
(transformPre GPRE I) 
  (fun _ s2 : state =>
   bool -> exists st2 : bool, (st2 = true :>bool -> I s2) /\ pre p pst s2 st2)
 (fun _ s2 : state =>
         bool ->
         exists st2 : bool,
           (st2 = true :>bool -> I s2) /\
           pre p pst s2 st2 /\ (st2 = true :>bool -> I s2)) 
 (fun _ s2 : state =>
   bool ->
   exists st2 : bool, (st2 = true :>bool -> I s2) /\ post p pst s2 st2)
   (fun _ s2 : state =>
         bool ->
         exists st2 : bool, (st2 = true :>bool -> I s2) /\ post p pst s2 st2)).

intros.
elim (H1 H2).
intros.
exists x.
destruct H3.
split.
assumption.
split.
assumption.
assumption.

intros.
elim (H1 H2).
intros.
exists x.
destruct H3.
split.
assumption.

assumption.
assumption.

Qed.  



