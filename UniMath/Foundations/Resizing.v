Require Export UniMath.Foundations.PartB.

(** In this file we implement the "resizing rules" of Voevodsky to make it possible to handle
    impredicative constructions.

    See https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/2011_Bergen.pdf
    for slides from a talk by Voevodsky entitled
    "Resizing Rules - their use and semantic justification" *)

(** This file is the only file in UniMath that is compiled with type-in-type. *)

(* The tactic exact_no_check is used to prevent constraints from being generated.
   Eventually Coq will, when used with type-in-type, generate no constraints.
   This will help us work around this issue with Coq: https://github.com/coq/coq/issues/8196
 *)

(* this is related to the rule Voevodsky calls RR1: *)
Definition ResizeProp@{i j|} (T : Type@{j}) : isaprop T -> Type@{i}.
Proof.
  exact_no_check (λ _:isaprop T, T).
Defined.

(* this is related to the rule Voevodsky calls RR5: *)
Definition ResizeType@{i j k|i<=k, j<=k} {S : Type@{i}} (T : Type@{j}) : weq@{k} S T -> Type@{i}.
Proof.
  exact_no_check (λ _:weq@{k} S T, T).
Defined.
