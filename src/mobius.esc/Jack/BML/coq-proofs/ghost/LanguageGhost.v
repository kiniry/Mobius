(*Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Require Import BasicDef. *)
Require  Import BasicDef.
Export BasicDef.


Inductive Gstmt  : Type :=
 | GAffect  : var      -> expr -> Gstmt
 | GIf          : expr    -> Gstmt -> Gstmt -> Gstmt
 | GWhile  : expr    -> Gstmt -> Gstmt
 | GSseq   : Gstmt -> Gstmt -> Gstmt
 | GSkip    : Gstmt 	
 | GSet      : gVar   -> gExpr -> Gstmt.

Inductive progG : Type :=
 | GProg : Gstmt ->  progG.

(**************************************************************************************************************)



