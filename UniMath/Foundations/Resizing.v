Require Export UniMath.Foundations.PartB.

(** In this file we implement the "resizing rules" of Voevodsky to make it possible to handle
    impredicative constructions.

    See https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/2011_Bergen.pdf
    for slides from a talk by Voevodsky entitled
    "Resizing Rules - their use and semantic justification" *)

(** This file is the only file in UniMath that is compiled with type-in-type. *)

(* this is related to the rule Voevodsky calls RR1: *)
Definition ResizeProp@{i j|i <j} (T : Type@{j}) : isaprop T -> Type@{i} := λ _, T.

(* this is related to the rule Voevodsky calls RR5: *)
Definition ResizeType@{i j|i <j} {S : Type@{i}} (T : Type@{j}) : weq@{j} S T -> Type@{i} := λ _, T.
