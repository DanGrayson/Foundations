Require Export UniMath.MoreFoundations.Notations.
Require Export UniMath.MoreFoundations.Propositions.

Definition HLevel_to_type n : HLevel n -> UU := pr1.

Coercion HLevel_to_type : HLevel >-> UU.

Definition HLevelPair n (X:UU) : isofhlevel n X -> HLevel n := λ i, X,,i.

Section Squashing.

  Local Notation "| a |" := (hinhpr a) (at level 20).

  Definition const {X:UU} {Y:UU} (f : X -> Y) : UU := ∏ x x', f x = f x'.

  Corollary const_transport' {X:UU} {Y:UU} (f : X -> Y) (c : const f) :
    ∏ x x' x'' (p : x' = x''), maponpaths f p = ! c x x' @ c x x''.
  Proof.
    intros. induction p. apply pathsinv0, pathsinv0l.
  Defined.

  Lemma const_loop {X:UU} {Y:UU} (f : X -> Y) :
    const f -> ∏ x x', const (@maponpaths X Y f x x').
  Proof.
    intros c x x' p p'.
    assert (Q := const_transport' f c x x x' p).
    assert (Q' := const_transport' f c x x x' p').
    exact (Q @ !Q').
  Defined.

  Definition squash_to_HLevel_2_full {X : UU} {Y : HLevel 2} (f : X -> Y) :
    const f -> ∥ X ∥ -> iscontr (image f).
  Proof.
    intros c w.
    apply isaprop_for_iscontr.
    { apply isapropsubtype; intros y y' j j'.
      apply (squash_to_prop j (pr2 Y _ _)); clear j; intros [j k].
      apply (squash_to_prop j' (pr2 Y _ _)); clear j'; intros [j' k'].
      exact (!k @ c j j' @ k'). }
    intros i. apply (squash_to_prop w i).
    intro x. exists (f x). apply hinhpr. now exists x.
  Defined.

  Definition squash_to_HLevel_2 {X : UU} {Y : HLevel 2} (f : X -> Y) :
    const f -> ∥ X ∥ -> Y.
  Proof.
    (* compare with the proof of squash_to_hSet *)
    intros c w. exact (pr11 (squash_to_HLevel_2_full f c w)).
  Defined.

  Lemma squash_to_HLevel_2_eqn {X : UU} {Y : HLevel 2} (f : X -> Y) (c : const f) :
    squash_to_HLevel_2 f c ∘ (λ x, |x|) = f.
  Proof.
    reflexivity.
  Defined.

  Definition squash_to_HLevel_3 {X : UU} {Y : HLevel 3}
             (f : X -> Y) (c : const f) :
    (∏ x x' x'', c x x'' = c x x' @ c x' x'') -> ∥ X ∥ -> Y.
  (** This is a special case of a theorem in
      "The General Universal Property of the Propositional Truncation"
      by Nicolai Kraus, at https://arxiv.org/abs/1411.2682 *)
  Proof.
    intros trans xx.
    (* guided homotopies *)
    set (G := (∑ (y:Y) (g : ∏ x, f x = y), (∏ x x', g x = c x x' @ g x'))).
    apply (pr1 : G -> _); change G. apply (squash_to_prop xx).
    { change (isaprop G). apply invproofirrelevance; intros [y [g q]] [y' [g' q']].
      transparent assert (eyy' : (y = y')).
      { use (squash_to_set (pr2 Y _ _) _ _ xx).
        { intros x. exact (! g x @ g' x). }
        { intros x x'; change (! g x @ g' x = ! g x' @ g' x').
          rewrite (q x x'), (q' x x'). rewrite pathscomp_inv. rewrite <- path_assoc.
          apply maponpaths. rewrite path_assoc. now rewrite pathsinv0l. } }
      assert (E' : ∏ x, eyy' = ! g x @ g' x).
      { intros x. now induction (ishinh_irrel x xx). }
      assert (E := (eyy',,E') : ∑ eyy' : y = y', ∏ x, eyy' = ! g x @ g' x).
      clear E' eyy'. induction E as [eyy' eqn]. induction eyy'. apply maponpaths.
      assert (l : g = g').
      { apply funextsec; intros x. rewrite <- (pathscomp0rid (g x)).
        rewrite (eqn x). rewrite path_assoc. now rewrite pathsinv0r. }
      clear eqn. induction l. apply maponpaths.
      { apply funextsec; intros x; apply funextsec; intros x'.
        exact (pr1 (pr2 Y _ _ _ _ _ _)). } }
    intros x. exists (f x). use tpair.
    - intros x'. apply c.
    - intros x' x''. apply trans.
  Defined.

  Lemma squash_to_HLevel_3_eqn {X : UU} {Y : HLevel 3} (f : X -> Y) (c : const f)
    (comp: ∏ x x' x'', c x x'' = c x x' @ c x' x'') :
    squash_to_HLevel_3 f c comp ∘ (λ x, |x|) = f.
  Proof.
    reflexivity.
  Defined.

End Squashing.
