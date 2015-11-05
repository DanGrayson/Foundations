Require Export UniMath.Foundations.Basics.PartC.

(* an experiment on one of the ideas in ssreflect: *)
Inductive ref (P:UU) : bool -> UU :=
| refT : P -> ref P true
| refF : ¬P -> ref P false.

Lemma A (P:UU) (i:isaprop P) : isaprop (Σ b, ref P b).
Proof.
  (* uses [funextempty] *)
  apply invproofirrelevance.
  intros [b r] [c s].
  induction r as [p|np].
  - induction s as [q|nq].
    + apply maponpaths, maponpaths, i.
    + contradicts p nq.
  - induction s as [q|nq].
    + contradicts np q.
    + apply maponpaths, maponpaths.
      apply funextempty.
Defined.

Lemma B (P:UU) (i:isaprop P) : (Σ b, ref P b) ≃ P ⨿ ¬ P.
Proof.
  apply weqiff.
  { split.
    - intros [b r]. induction r as [p|np].
      + exact (ii1 p).
      + exact (ii2 np).
    - intros c. induction c as [p|np].
      + exact (true,,refT P p).
      + exact (false,,refF P np). }
  { now apply A. }
  { now apply isapropdec. }
Defined.

(*
Local Variables:
compile-command: "make -C ../.. UniMath/Experiments/Reflect.vo"
End:
*)
