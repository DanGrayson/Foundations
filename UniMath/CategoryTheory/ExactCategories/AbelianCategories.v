(** * Abelian categories as exact categories  *)

(** We show an abelian category, equipped with the exact sequences as the exact ones,
    is an exact category. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.AbelianToAdditive.
Require Export UniMath.CategoryTheory.ExactCategories.ExactCategories.

Local Open Scope cat.
Local Open Scope logic.
Local Open Scope abgrcat.
(* some of these might be appropriate upstream: *)
Local Arguments isZero {_} _.
Local Arguments BinDirectSumOb {_ _ _}.
Local Arguments to_binop {_ _ _}.
Local Arguments grinv {_}.
Local Arguments BinDirectSum {_}.
Local Arguments to_Pr1 {_ _ _} _.
Local Arguments to_Pr2 {_ _ _} _.
Local Arguments to_In1 {_ _ _} _.
Local Arguments to_In2 {_ _ _} _.
Local Arguments to_BinOpId {_ _ _ _ _ _ _ _}.
Local Arguments to_IdIn1 {_ _ _ _ _ _ _ _}.
Local Arguments to_IdIn2 {_ _ _ _ _ _ _ _}.
Local Arguments to_Unel1 {_ _ _ _ _ _ _ _}.
Local Arguments to_Unel2 {_ _ _ _ _ _ _ _}.
Local Arguments MorphismPair : clear implicits.
Local Arguments morphism_from_iso {_ _ _}.
Local Arguments ToBinDirectSum {_ _ _} _ {_}.
Local Arguments isBinDirectSum {_ _ _ _}.

(* move upstream *)
Definition AbelianCategory := ∑ M:AbelianPreCat, has_homsets M.
Coercion AbelianCategory_to_AbelianPreCat (M:AbelianCategory) := pr1 M.

Definition isQuasiabelian (M:AdditiveCategory) : hProp :=
  (∀ (A B:M) (f:A-->B), hasKernel f) ∧
  (∀ (A B:M) (f:A-->B), hasCokernel f) ∧
  (∀ (A B A':M) (f:A-->B) (g:A-->A'), isAKernel f ⇒ ∃ (PO : Pushout f g), isAKernel (PushoutIn2 PO)) ∧
  (∀ (B C C':M) (f:B-->C) (g:C'-->C), isACokernel f ⇒ ∃ (PB : Pullback f g), isACokernel (PullbackPr2 PB)).

(* move upstream *)
Coercion AbelianPreCatToAdditiveCategory (M:AbelianCategory) : CategoryWithAdditiveStructure.
Proof.
  exact (AbelianToAdditive M (pr2 M)).
Defined.

(* move upstream *)
Coercion CategoryWithAdditiveStructure_to_AdditiveCategory (M : CategoryWithAdditiveStructure) : AdditiveCategory.
Proof.
  exists M. split.
  - apply hinhpr. apply to_Zero.
  - intros A B. apply hinhpr. apply to_BinDirectSums.
Defined.

Lemma AbelianCategoryIsQuasiAbelian (M:AbelianCategory) : isQuasiabelian M.
Proof.
Abort.


