(** * Additive categories as exact categories  *)

(** We show an additive category, equipped with the split sequences as the exact ones,
    is an exact category. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
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

Section SplitSequences.
  Definition isSplit2 {M:PreAdditive} {A B C:M} (i:A-->B) (q:B-->C) : hProp :=
    ∃ (p:A<--B) (j:B<--C), isBinDirectSum i j p q.
  Lemma commax_hom {M:PreAdditive} {A B:M} (f g:A-->B) : f+g = g+f.
  Proof.
    exact (commax (A-->B) f g).
  Qed.
  Section Foo.
    Goal ∏ {M:PreAdditive} {A B C:M} (i:A-->B) (p:B-->C),
      isSplit2 (M:=M) i p = isSplit2 (M := oppositePreAdditive M) p i.
    Proof.
      Fail reflexivity.
      intros M A B C k r.
      unfold isSplit2, isBinDirectSum; cbn; rewrite rewrite_op.
      (* do we need this? *)
    Abort.
  End Foo.
  Lemma opposite_isSplit2 {M:PreAdditive} {A B C:M} (i:A-->B) (p:B-->C) :
    isSplit2 i p -> isSplit2 (M := oppositePreAdditive M) p i.
  Proof.
    intros s.
    Fail exact s.               (* sigh *)
    use (hinhfun _ s); intros [q [j jq]]. exists j. exists q.
    exists (to_IdIn2 jq). exists (to_IdIn1 jq).
    exists (to_Unel1 jq). exists (to_Unel2 jq).
    rewrite commax_hom. exact (to_BinOpId' jq).
  Qed.
  Definition isSplit {M:PreAdditive} (P : MorphismPair M) : hProp := isSplit2 (Mor1 P) (Mor2 P).
  Lemma opposite_isSplit {M:PreAdditive} (P : MorphismPair M) :
    isSplit P -> isSplit (M:=oppositePreAdditive M) (MorphismPair_opp P).
  Proof.
    exact (opposite_isSplit2 _ _).
  Qed.
  Definition isSplitMonomorphism {M:PreAdditive} {A B:M} (i : A --> B) : hProp :=
    ∃ C (p : B --> C), isSplit2 i p.
  Definition isSplitEpimorphism {M:PreAdditive} {B C:M} (p : B --> C) : hProp :=
    ∃ A (i : A --> B), isSplit2 i p.
  Lemma opposite_isSplitMonomorphism {M:PreAdditive} {A B:M} (i : A --> B) :
    isSplitMonomorphism i -> isSplitEpimorphism (M:=oppositePreAdditive M) i.
  Proof.
    intros s. use (hinhfun _ s); clear s. intros [C [p s]].
    exists C. exists p. exact (opposite_isSplit2 _ _ s).
  Qed.
  Lemma opposite_isSplitEpimorphism {M:PreAdditive} {A B:M} (p : A --> B) :
    isSplitEpimorphism p -> isSplitMonomorphism (M:=oppositePreAdditive M) p.
  Proof.
    intros s. use (hinhfun _ s); clear s. intros [C [i s]].
    exists C. exists i. exact (opposite_isSplit2 _ _ s).
  Qed.
  Lemma DirectSumToSplit {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) : isSplit2 (to_In1 AB) (to_Pr2 AB).
  Proof.
    exact (hinhpr (π₁,, ι₂,, BinDirectSum_isBinDirectSum M AB)).
  Qed.
  Lemma DirectSumToSplit' {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) : isSplit2 (to_In2 AB) (to_Pr1 AB).
  Proof.
    exact (hinhpr(π₂,,ι₁,,BinDirectSum_isBinDirectSum M (reverseBinDirectSum AB))).
  Qed.
  Lemma IsomorphicToSplit {M:PreAdditive} (P Q : MorphismPair M) :
    MorphismPairIsomorphism P Q ⇒ isSplit P ⇒ isSplit Q.
  Proof.
    intros [f' [f [f'' [[e _] [e' _]]]]] ex.
    apply (squash_to_hProp ex); clear ex; intros [q [j su]]; apply hinhpr.
    exists (z_iso_inv f · q · f').
    exists (z_iso_inv f'' · j · f).
    split.
    { intermediate_path (z_iso_inv f' · Mor1 P · q · f').
      { rewrite 2 assoc. apply (maponpaths (λ k, k·f')).
        apply (maponpaths (λ k, k·q)). apply pathsinv0.
        apply z_iso_inv_on_right. rewrite assoc. apply z_iso_inv_on_left. exact e. }
      { rewrite 2 assoc'. rewrite (assoc _ q _).
        intermediate_path (z_iso_inv f' · (identity _ · f')).
        { apply maponpaths. apply (maponpaths (λ k, k·f')). exact (to_IdIn1 su). }
        { rewrite id_left. apply z_iso_after_z_iso_inv. } } }
    split.
    { rewrite assoc'. rewrite e'.  rewrite assoc. rewrite (assoc' _ j _).
      apply wrap_inverse. apply (to_IdIn2 su). }
    split.
    { assert (r := to_Unel1 su); unfold to_unel in r.
      assert (r' := maponpaths (λ t, t · f'') r); cbn in r'; clear r.
      rewrite assoc' in r'. rewrite <- e' in r'. rewrite assoc in r'.
      rewrite <- e in r'. assert (r'' := maponpaths (λ t, z_iso_inv f' · t) r'); clear r'; cbn in r''.
      rewrite 2 assoc in r''. rewrite z_iso_after_z_iso_inv in r''.
      rewrite assoc' in r''. rewrite id_left in r''. rewrite zeroLeft,zeroRight in r''.
      exact r''. }
    split.
    { rewrite 2 assoc. rewrite (assoc' _ f _). rewrite z_iso_inv_after_z_iso.
      rewrite id_right. rewrite (assoc' _ j _). rewrite (to_Unel2 su).
      unfold to_unel. rewrite zeroRight, zeroLeft. reflexivity. }
    { apply (cancel_z_iso' f). rewrite id_right. rewrite rightDistribute.
      rewrite 3 (assoc f). rewrite z_iso_inv_after_z_iso, id_left.
      rewrite assoc'. rewrite e. rewrite assoc.
      rewrite (assoc f). rewrite e'. rewrite (assoc' _ f'').
      rewrite 2 (assoc f''). rewrite z_iso_inv_after_z_iso, id_left. rewrite assoc.
      rewrite <- leftDistribute. rewrite (to_BinOpId' su). rewrite id_left. reflexivity. }
  Qed.
  Lemma DirectSumToKernel {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) : isKernel' (to_In1 AB) (to_Pr2 AB).
  Proof.
    apply makeMonicKernel.
    - apply to_In1_isMonic.
    - exact (to_Unel1 AB).
    - intros T h e. exists (h · π₁). unfold eqset; cbn. refine (_ @ id_right _).
      rewrite <- (to_BinOpId AB). rewrite rewrite_op. rewrite rightDistribute.
      rewrite assoc'. rewrite (assoc _ π₂ _). rewrite e. rewrite zeroLeft. rewrite runax. reflexivity.
  Defined.
  Lemma DirectSumToCokernel {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) : isCokernel' (to_In1 AB) (to_Pr2 AB).
  Proof.
    apply makeEpiCokernel.
    - apply to_Pr2_isEpi.
    - exact (to_Unel1 AB).
    - intros T h e. exists (ι₂ · h). unfold eqset; cbn. refine (_ @ id_left _).
      rewrite <- (to_BinOpId AB). rewrite rewrite_op. rewrite leftDistribute.
      rewrite assoc. rewrite (assoc' _ ι₁ _). rewrite e. rewrite zeroRight. rewrite lunax. reflexivity.
  Defined.
  Lemma isSplitToKernelCokernelPair {M:PreAdditive} {A B C:M} (i:A-->B) (p:B-->C) :
    isSplit2 i p -> isKernelCokernelPair i p.
  Proof.
    intros sp.
    apply (squash_to_hProp sp); clear sp; intros [j [q issum]].
    set (S := mk_BinDirectSum _ _ _ _ _ _ _ _ issum).
    exact (DirectSumToKernel S,,DirectSumToCokernel S).
  Qed.
  Lemma ComposeSplitMono {M:AdditiveCategory} {A B C : M} (i : A --> B) (j : B --> C) :
    isSplitMonomorphism i ⇒ isSplitMonomorphism j ⇒ isSplitMonomorphism (i · j).
  Proof.
    intros s t.
    apply (squash_to_hProp s); clear s; intros [P [p ip]];cbn in P.
    apply (squash_to_hProp ip); clear ip; intros [p' [i' ip]].
    change (hProptoType (isBinDirectSum i i' p' p)) in ip.
    apply (squash_to_hProp t); clear t; intros [Q [q jq]];cbn in Q.
    apply (squash_to_hProp jq); clear jq; intros [q' [j' jq]].
    change (hProptoType (isBinDirectSum j j' q' q)) in jq.
    apply (squash_to_hProp (to_hasBinDirectSums P Q)); intros PQ.
    apply hinhpr;unfold ExactCategoryDataToAdditiveCategory,pr1.
    exists PQ.
    exists (q' · p · ι₁ + q · ι₂).
    apply hinhpr.
    exists (q' · p').
    exists (π₁ · i' · j + π₂ · j').
    repeat split; unfold eqset; cbn; rewrite ? rewrite_op.
    { rewrite assoc'. rewrite (assoc j). rewrite (to_IdIn1 jq). rewrite id_left.
      rewrite (to_IdIn1 ip). reflexivity. }
    { rewrite rightDistribute, 2 leftDistribute.
      rewrite (assoc' q'). rewrite (assoc' _ j).
      rewrite (assoc j). rewrite (to_IdIn1 jq). rewrite id_left.
      rewrite assoc'. rewrite (assoc i'). rewrite (to_IdIn2 ip). rewrite id_left.
      rewrite (assoc _ q'). rewrite (assoc' _ j'). rewrite (to_Unel2 jq); unfold to_unel.
      rewrite zeroRight, zeroLeft, runax.
      rewrite (assoc' _ j). rewrite (assoc j). rewrite (to_Unel1 jq). unfold to_unel.
      rewrite zeroLeft, zeroRight, lunax. rewrite assoc'.
      rewrite (assoc j'). rewrite (to_IdIn2 jq). rewrite id_left. apply (to_BinOpId PQ). }
    { rewrite rightDistribute. rewrite assoc'. rewrite (assoc' q').
      rewrite (assoc j). rewrite (to_IdIn1 jq). rewrite id_left.
      rewrite assoc. rewrite (to_Unel1 ip); unfold to_unel.
      rewrite zeroLeft. rewrite lunax. rewrite assoc'.
      rewrite (assoc j). rewrite (to_Unel1 jq); unfold to_unel.
      rewrite zeroLeft, zeroRight. reflexivity. }
    { rewrite leftDistribute. rewrite assoc'. rewrite (assoc j).
      rewrite (to_IdIn1 jq). rewrite id_left. rewrite (assoc' _ i').
      rewrite (to_Unel2 ip); unfold to_unel.
      rewrite zeroRight. rewrite lunax. rewrite assoc'.
      rewrite (assoc j'). rewrite (to_Unel2 jq);unfold to_unel.
      rewrite zeroLeft, zeroRight. reflexivity. }
    { rewrite rightDistribute, 2 leftDistribute. rewrite assoc.
      rewrite (assoc' _ i'). rewrite (assoc' _ ι₁). rewrite (assoc ι₁).
      rewrite (to_IdIn1 PQ). rewrite id_left. rewrite assoc.
      rewrite (assoc' q). rewrite (assoc _ _ (i' · j)).
      rewrite (to_Unel2 PQ); unfold to_unel. rewrite zeroLeft, zeroRight, runax.
      rewrite <- assocax. rewrite <- (leftDistribute _ _ j).
      rewrite 2 (assoc' q'). rewrite <- (rightDistribute q').
      rewrite (to_BinOpId' ip). rewrite id_right.
      rewrite (assoc' _ ι₁). rewrite (assoc ι₁). rewrite (to_Unel1 PQ); unfold to_unel.
      rewrite zeroLeft, zeroRight, lunax. rewrite (assoc' q).
      rewrite (assoc ι₂). rewrite (to_IdIn2 PQ).
      rewrite id_left. exact (to_BinOpId' jq). }
  Qed.
  Lemma ComposeSplitEpi {M:AdditiveCategory} {A B C : M} (p : A --> B) (q : B --> C) :
    isSplitEpimorphism p ⇒ isSplitEpimorphism q ⇒ isSplitEpimorphism (p · q).
  Proof.
    intros r s.
    exact (opposite_isSplitMonomorphism _
             (ComposeSplitMono (M:=oppositeAdditiveCategory M)
                               _ _ (opposite_isSplitEpimorphism _ s) (opposite_isSplitEpimorphism _ r))).
  Qed.
  Lemma PullbackSplitEpi {M:AdditiveCategory} {A A'' C : M} (q : A --> A'') (g : C --> A'') :
    isSplitEpimorphism q -> ∃ PB : Pullback q g, isSplitEpimorphism (PullbackPr2 PB).
  Proof.
    intros s.
    apply (squash_to_hProp s); clear s; intros [A' [i e]].
    apply (squash_to_hProp e); clear e; intros [p [j e]].
    apply (squash_to_hProp (to_hasBinDirectSums A' C)); intros A'C.
    apply hinhpr.
    use tpair.
    - use tpair.
      + exists A'C. exists (π₁ · i + π₂ · g · j). exact π₂.
      + simpl. rewrite rewrite_op.
        use tpair.
        * rewrite leftDistribute. rewrite (assoc' _ j q). rewrite (to_IdIn2 e).
          rewrite id_right. rewrite (assoc' _ i q). rewrite (to_Unel1 e); unfold to_unel.
          rewrite zeroRight, lunax. reflexivity.
        * intros T r s eqn. apply iscontraprop1.
          { apply invproofirrelevance. intros h k.
            apply subtypeEquality.
            { intros l. apply isapropdirprod;apply to_has_homsets. }
            induction h as [h [H H']], k as [k [K K']]. simpl.
            rewrite <- (id_right h), <- (id_right k). rewrite <- (to_BinOpId' A'C).
            rewrite 2 rightDistribute. rewrite 4 assoc. rewrite H', K'.
            apply (maponpaths (λ z, z + s · ι₂)). rewrite rightDistribute in H, K.
            rewrite 3 assoc in H, K. rewrite H' in H. rewrite K' in K.
            apply (maponpaths (λ z, z · ι₁)).
            apply (to_In1_isMonic _ (mk_BinDirectSum _ _ _ _ _ _ _ _ e)).
            change (h · π₁ · i = k · π₁ · i). apply (grrcan (T-->A) (s · g · j)).
            exact (H @ !K). }
          exists (r · p · ι₁ + s · ι₂).
          split.
          { rewrite leftDistribute, 2 rightDistribute.
            rewrite assoc'. rewrite (assoc _ _ i). rewrite (to_IdIn1 A'C). rewrite id_left.
            rewrite (assoc' (r · p)). rewrite 2 (assoc ι₁).
            rewrite (to_Unel1 A'C); unfold to_unel. rewrite 2 zeroLeft, zeroRight, runax.
            rewrite (assoc' s). rewrite (assoc ι₂). rewrite (to_Unel2 A'C); unfold to_unel.
            rewrite zeroLeft, zeroRight, lunax. rewrite 2 assoc. rewrite (assoc' s).
            rewrite (to_IdIn2 A'C). rewrite id_right. rewrite (!eqn).
            rewrite 2 assoc'. rewrite <- (rightDistribute r). rewrite (to_BinOpId' e).
            apply id_right. }
          { rewrite leftDistribute. rewrite (assoc' (r · p)). rewrite (to_Unel1 A'C); unfold to_unel.
            rewrite zeroRight, lunax. rewrite assoc'. rewrite (to_IdIn2 A'C).
            apply id_right. }
    - cbn. exact (hinhpr(A',,ι₁,, hinhpr (π₁,,ι₂,,BinDirectSum_isBinDirectSum _ A'C))).
  Qed.
  Lemma PushoutSplitMono {M:AdditiveCategory} {A A' C : M} (i : A' --> A) (g : A' --> C) :
    isSplitMonomorphism i ⇒ ∃ PO : Pushout i g, isSplitMonomorphism (PushoutIn2 PO).
  Proof.
    intros s.
    assert (Q := @PullbackSplitEpi (oppositeAdditiveCategory M) _ _ _ i g (opposite_isSplitMonomorphism _ s)).
    use (hinhfun _ Q); clear Q; intros [A''C epi].
    exists (A''C).
    exact (opposite_isSplitEpimorphism _ epi).
  Qed.
End SplitSequences.

Lemma AdditiveExactnessProperties (M:AdditiveCategory) : ExactCategoryProperties (M,,isSplit).
Proof.
  split;unfold ExactCategoryDataToAdditiveCategory,pr1.
  - split.
    { intros P Q. apply IsomorphicToSplit. }
    { intros P Q i e. use IsomorphicToSplit.
      2 : { exact (InverseMorphismPairIsomorphism i). }
      exact e. }
  - split.
    { split.
      { intros A. apply (squash_to_hProp (to_hasZero M)); intros Z.
        apply hinhpr. exists Z. set (Q := TrivialDirectSum Z A).
        exact (to_Pr2 Q,, DirectSumToSplit Q). }
      { intros A. apply (squash_to_hProp (to_hasZero M)); intros Z.
        apply hinhpr. exists Z. set (Q := TrivialDirectSum' Z A).
        exact (to_In1 Q,, DirectSumToSplit Q). } }
    split.
    { intros P. exact (isSplitToKernelCokernelPair (Mor1 P) (Mor2 P)). }
    split.
    { split.
      { exact (@ComposeSplitMono M). }
      { exact (@ComposeSplitEpi M). } }
    { split.
      { exact (@PullbackSplitEpi M). }
      { exact (@PushoutSplitMono M). } }
Defined.
Definition AdditiveToExact : AdditiveCategory -> ExactCategory
  := λ M, mk_ExactCategory (M,,isSplit) (AdditiveExactnessProperties M).
Lemma additive_exact_opposite {M:AdditiveCategory} :
  AdditiveToExact (oppositeAdditiveCategory M) = oppositeExactCategory (AdditiveToExact M).
Proof.
  intros. apply subtypeEquality_prop. apply pair_path_in2.
  apply funextsec; intros P. apply hPropUnivalence.
  * exact (opposite_isSplit P).
  * exact (opposite_isSplit (MorphismPair_opp P)).
Qed.
