Require Export UniMath.Foundations.PartB.

(** In this file we implement the "resizing rules" of Voevodsky to make it possible to handle
    impredicative constructions.

    See https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/2011_Bergen.pdf
    for slides from a talk by Voevodsky entitled
    "Resizing Rules - their use and semantic justification" *)

(** This file is the only file in UniMath that is compiled with type-in-type. *)

Section A.

  Universe i j.

  (* If we don't impose this constraint, Coq generates the constraint j <= i for us, which excludes
     the cases we want. *)
  Constraint i < j.

  (* this is related to the rule Voevodsky calls RR1: *)
  Definition ResizeProp@{} (T : Type@{j}) : isaprop T -> Type@{i} := λ _, T.

  (* this is related to the rule Voevodsky calls RR5: *)
  Definition ResizeType@{} {S : Type@{i}} (T : Type@{j}) : weq@{j} S T -> Type@{i} := λ _, T.

End A.
