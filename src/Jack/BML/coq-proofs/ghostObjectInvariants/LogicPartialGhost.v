Require Import LanguageGhost.


Export LanguageGhost.


(*LOGIC IN A SP STYLE WITH EXPLICITE CONSEQUENCE RULE *)
Open Scope Z_scope.




 
(*RULES FOR REASONING OVER PROGRAMS AND ASSERTIONS. THIS ASSERTIONS MUST HOLD IN 
  THE TERMINAL STATE  OF THE STATEMENT EXECUTION. THUS, THIS LOGIC RULES EXPRESS PARTIAL 
  CORRECTNESS. METHODS ARE PROVIDED WITH SPECIFICATIONS WHICH STATE
   WHAT MUST HOLD IN THE TERMINAL STATE OF A METHOD. THE SPECIFICATIONS ARE GIVEN 
   BY THE MAPPING FROM METHOD NAMES TO ASSERTIONS. 
  THE CONSEQUENCE RULE IS IMPLICITE AS IT IS INLINED IN EVERY RULE*)
Inductive GRULET (MS : gMethPost) (MPre : gMethPre)
     (I : Invariant):  gAssertion -> gStmt -> gAssertion -> Prop :=
|  GAffectRule : forall   x e  (pre pre1 post1 post : gAssertion)  , 
    (*implicite consequence rule*)
    (forall  p s stp st, pre p stp s st   -> pre1 p stp s st  ) -> 
    (forall  p s stp st, post1 p stp s st    -> post p stp s st  ) -> 
    (forall  p  (s : state) stp st , pre1 p stp s st -> st = false) -> 
    (forall p ( s1 s2: state) stp st1 st2   , 
         pre1 p stp s1 st1  /\  s2 = update s1 x (eval_expr s1  e)   -> post1 p stp s2 st2)  ->
    GRULET MS MPre  I pre  (GAffect x e) post 
 
 | GIfRule : forall   e (stmtT stmtF: gStmt ) (  pre pre1 pre2 post  post1  post2: gAssertion) , 
    (forall p s pst st, pre p pst s st -> pre1  p pst s st) -> 
    (forall p s pst st, pre p pst s st -> pre2  p pst s st) ->
    (forall p s pst st, post1 p pst s st  -> post p pst s st) ->
    (forall p s pst st, post2 p pst s st -> post p pst  s st) ->
    (forall p pst,
     GRULET MS MPre I
     (fun s1 st1 s2 st2 => pre1 p pst s2 st2 /\ (eval_expr s2  e) <>0 )  stmtT (fun s1 st1  s2 st2 =>  post1 p pst s2 st2)) ->
    (forall p pst,
     GRULET MS MPre I (fun s1 st1 s2 st2 => pre2 p pst s2 st2 /\ (eval_expr s2  e) = 0)  stmtF 
     (fun s1 st1 s2 st2 =>  post2 p pst s2 st2) )->
 
    GRULET MS MPre I pre (GIf e stmtT stmtF) post 

 | GWhileRule : forall   (stmt : gStmt ) e (pre pre1 li post1 post : gAssertion),
    (forall p s pst st, pre p pst s st -> pre1 p pst s st) -> 
    (forall p s pst st , post1 p pst s st -> post p pst s st) ->
    (*the real while rule*)
    (forall p s  pst st, pre1 p pst  s st -> li p pst  s st ) -> 
    (forall p s pst st, li  p pst  s st  /\ (eval_expr s  e) = 0 -> post1 p pst  s st) ->
    (forall p pst,
     GRULET MS MPre I (fun s1 st1 s2 st2 => li p pst s2 st2 /\ (eval_expr s2  e) <> 0 )   stmt
     (fun s1 st1 s2 st2 => li p pst s2 st2)) ->

   GRULET MS MPre I  pre (GWhile e stmt) post  

 |  GSeqRule: forall  (stmt1 stmt2: gStmt )
    (pre pre1 inter post1 post : gAssertion) , 
    (forall  p s pst st, pre p pst s st  -> pre1 p pst s st ) -> 
    (forall  p s pst st, post1 p pst s st -> post p pst s st  ) ->                             
    (forall p pst,  
     GRULET MS MPre  I (fun  s1 st1 s2  st2=> pre1 p pst s2 st2) stmt1 (fun s1  st1 s2 st2 => inter p pst s2 st2) ) -> 
    (forall p pst,
     GRULET MS MPre I (fun s1 st1 s2 st2 => inter p pst s2 st2) stmt2 (fun s1 st1 s2 st2  => post1 p pst s2 st2) )  -> 
    (*forall p s,  inter1 p  s -> inter2 p s -> *) 
    GRULET MS MPre  I pre (GSseq stmt1 stmt2) post

 | GSkipRule:   forall ( pre pre1 post1 post: gAssertion) ,
   (forall  p s pst st, pre p pst s st  -> pre1 p pst s st ) -> 
   (forall  p s pst st, post1 p pst s st -> post p pst s st  ) ->         
   (forall p s1 s2  pst st1 st2 , pre p pst s1 st1 -> s1 = s2 -> post p pst s2  st2) ->
   GRULET MS MPre    I pre GSkip  post

 | GCallRule : forall   ( mName : methodNames )  (pre  post   : gAssertion )  , 
   (forall p s pst st,   pre p pst s st  -> (MPre mName ) s  st   ) ->
   (forall p s1 s2 pst st1 st2, pre p pst s1 st1 ->  ( MS mName ) s1 st1  s2 st2  -> post p pst s2 st2  ) ->
   GRULET MS MPre  I  pre (GCall mName )  post

 | PackRule : forall ( pre  post   : gAssertion ), 
   ( forall (p s: state ) pst st,  pre p pst s st -> st= false  ) ->
   ( forall (p s: state ) pst st,  pre p pst s st -> I  s ) ->
   ( forall (p s1 s2: state ) pst st1 st2, pre p pst s1 st1 /\ s1 = s2 /\ 
      st2 = true -> post p pst s2 st2) ->
    GRULET MS MPre I   pre Pack   post

  | UnpackRule : forall   ( pre post   : gAssertion ) , 
   (forall (p s: state ) pst st,  pre p pst s st -> st= true  ) ->
   (forall (p s1 s2: state ) pst st1 st2, pre  p pst s1 st1 /\ s1 = s2 /\  
      st2 = false -> post p pst s2 st2) ->
    GRULET MS MPre   I   pre Unpack  post
 
 | Inv : forall (stmt : gStmt ) ( pre post   : gAssertion ), 
   (forall p pst,  GRULET MS MPre   I   
     (fun s1 st1 s2 st2 => pre p pst s2 st2  /\ (st2 = true -> I s2 ) ) stmt
     (fun s1 st1 s2 st2  => post p pst s2 st2  ) ) ->
   GRULET MS MPre   I pre stmt post. 
 
