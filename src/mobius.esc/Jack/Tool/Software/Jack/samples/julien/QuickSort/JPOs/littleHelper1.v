Require Import Bool.
Require Import ZArith.
Require Import Zdiv.
Open Scope Z_scope.

(* Primitive Type Definition:*)
Definition c_minbyte := -128.
Definition c_maxbyte := 127.
Definition c_minshort := -32768.
Definition c_maxshort := 32767.
Definition c_minint := -2147483648.
Definition c_maxint := 2147483647.
Definition c_minchar := 0.
Definition c_maxchar := 65535.
Definition c_minlong := -9223372036854775808.
Definition c_maxlong := 9223372036854775807.
Definition t_byteDom (n:Z): Prop := c_minbyte <= n /\ n <= c_maxbyte.
Definition t_shortDom (n:Z): Prop := c_minshort <= n /\ n <= c_maxshort.
Definition t_intDom (n:Z): Prop := c_minint <= n /\ n <= c_maxint.
Definition t_charDom (n:Z): Prop := c_minchar <= n /\ n <= c_maxchar.
Definition t_longDom (n:Z): Prop := c_minlong <= n /\ n <= c_maxlong.
Variable t_float : Set.
Variable F0 : t_float.
Variable Fle : t_float -> t_float -> Prop.


Definition t_byte := Z.
Definition t_short := Z.
Definition t_int := Z.
Definition t_char := Z.
Definition t_long := Z.


(* Arithmetic Operators *)
Definition j_add: t_int -> t_int -> t_int := Zplus.
Infix "+" := j_add: J_Scope.
Definition j_sub: t_int -> t_int -> t_int := Zminus.
Infix "-" := j_sub: J_Scope.
Definition j_mul: t_int -> t_int -> t_int := Zmult.
Infix "*" := j_mul: J_Scope.
Definition j_div: t_int -> t_int -> t_int := Zdiv.
Infix "/" := j_div: J_Scope.
Definition j_rem: t_int -> t_int -> t_int := Zmod.
Definition j_le: t_int -> t_int -> Prop := Zle.
Infix "<=" := j_le: J_Scope.
Definition j_gt: t_int -> t_int -> Prop := Zgt.
Infix ">" := j_gt: J_Scope.
Definition j_lt: t_int -> t_int -> Prop := Zlt.
Infix "<" := j_lt: J_Scope.
Definition j_ge: t_int -> t_int -> Prop := Zge.
Infix ">=" := j_ge: J_Scope.
Definition j_neg : t_int -> t_int := Zopp.
Variable j_shl : t_int -> t_int -> t_int.
Variable j_shr : t_int -> t_int -> t_int.
Variable j_ushr : t_int -> t_int -> t_int.
Variable j_and : t_int -> t_int -> t_int.
Variable j_or : t_int -> t_int -> t_int.
Variable j_xor : t_int -> t_int -> t_int.

(* Dummy Arithmetic Conversions *)
Definition j_convert := fun (min max:Z) =>
   let range :=  ((- min) + max ) in
       fun (a:Z) => 
          let n := (if (Zle_bool 0 a) then a
                    else  (a + ((((- a) / range) + 1) * range))) in
             if (Zle_bool (n mod range) max) then
                (n mod range)
             else ((n mod range) - range).
Definition j_int2char : t_int -> t_char := j_convert c_minchar c_maxchar.
Definition j_int2byte : t_int -> t_byte := j_convert c_minbyte c_maxbyte.
Definition j_int2short : t_int -> t_short := j_convert c_minshort c_maxshort.

Add Ring t_int j_add j_mul 1%Z 0%Z j_neg Zeq ZTheory
[ Zpos Zneg 0%Z xO xI 1%positive ].

