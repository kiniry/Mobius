Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Require Import BasicDef.

Export ZArith.
Export Bool.
Export BoolEq.
Export List.
Export BasicDef.


Inductive stmt  : Type :=
 | Affect : var -> expr -> stmt
 | If     :  expr -> stmt -> stmt -> stmt
 | While  : expr -> stmt -> stmt
 | Sseq   : stmt -> stmt -> stmt 
 | Skip : stmt.


Inductive prog : Type :=
 | Prog : stmt ->  prog.
