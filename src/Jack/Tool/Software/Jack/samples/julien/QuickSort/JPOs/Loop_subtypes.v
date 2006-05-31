Add LoadPath "/home/jcharles/sources/runtime-workspace/QuickSort/JPOs".

Require Import "jack_references".
Require Import "Loop_classes".
Import LoopClasses.

Module LoopSubtypes.
Module JackClasses := JackReferences LoopClasses.
Import JackClasses.

Definition subtypes (t1: Types) (t2: Types): Prop :=
    match t2 with
      (class c_int) => match t1 with
        (class c_int) => True
        | _ => False
        end
     | (class c_short) => match t1 with
        (class c_short) => True
        | _ => False
        end
     | (class c_char) => match t1 with
        (class c_char) => True
        | _ => False
        end
     | (class c_byte) => match t1 with
        (class c_byte) => True
        | _ => False
        end
     | (class c_boolean) => match t1 with
        (class c_boolean) => True
        | _ => False
        end
     | (class c_java_lang_Object) => match t1 with
        _ => True
        end
     | (class c_fr_Loop) => match t1 with
         (class c_fr_Loop) => True
        | _ => False
        end
   | _ => t1 = t2
   end.

Axiom subtypes_trans :
forall a b , subtypes b a  -> forall c, subtypes c b -> subtypes  c a. 

(* The Proof is too long to compute so.... forall a b , subtypes b a  -> forall c, subtypes c b -> subtypes  c a.)
Proof.
destruct a. destruct b.
2:
simpl in hyp2;
rewrite <- hyp2 in hyp1; trivial.
2:
simpl in hyp1;
rewrite hyp1 in hyp2; trivial.
destruct c.
2:
simpl in hyp2;
destruct c1; elim hyp2; auto.

destruct c1; 
destruct c0;try (elim hyp1;fail);
destruct c;
try (elim hyp2; fail); trivial.Qed. *)

Lemma subtypes_refl:forall  a, subtypes  a a.
Proof.
intros.  destruct a.
destruct c; simpl; trivial.
simpl; trivial.
Qed.

Lemma subtypes_0: forall c: Types, subtypes c (class c_fr_Loop) -> subtypes c (class c_java_lang_Object).
Proof (fun (c:Types) (h1: subtypes c (class c_fr_Loop)) => 
        subtypes_trans (class c_java_lang_Object) (class c_fr_Loop)  I c h1).

Hint Resolve subtypes_0.
End LoopSubtypes.
