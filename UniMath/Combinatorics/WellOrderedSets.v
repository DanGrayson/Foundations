(* -*- coding: utf-8 -*- *)

(** * Well Ordered Sets *)

(** In this file our goal is to prove Zorn's Lemma and Zermelo's Well-Ordering Theorem. *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.MoreFoundations.DecidablePropositions.
Require Import UniMath.MoreFoundations.Propositions.
Require Import UniMath.Combinatorics.OrderedSets.

Local Open Scope logic.
Local Open Scope prop.
Local Open Scope set.
Local Open Scope subtype.
Local Open Scope poset.

Delimit Scope tosubset with tosubset. (* subsets equipped with a well ordering *)
Local Open Scope tosubset.

Delimit Scope wosubset with wosubset. (* subsets equipped with a well ordering *)
Local Open Scope wosubset.

(** ** Totally ordered subsets of a set *)

Definition TotalOrdering (S:hSet) : hSet := ∑ (R : hrel_set S), isTotalOrder R.

Definition TOSubset_set (X:hSet) : hSet := ∑ (S:subtype_set X), TotalOrdering (carrier_set S).

Definition TOSubset (X:hSet) : UU := TOSubset_set X.

Definition TOSubset_to_subtype {X:hSet} : TOSubset X -> hsubtype X
  := pr1.

Coercion TOSubset_to_subtype : TOSubset >-> hsubtype.

Definition TOSrel {X:hSet} (S : TOSubset X) : hrel (carrier_set S) := pr12 S.

Definition TOpartial {X:hSet} (S : TOSubset X) : isPartialOrder (TOSrel S) := pr122 S.

Definition TOtotal {X:hSet} (S : TOSubset X) : isTotalOrder (TOSrel S) := pr22 S.

(* phase this out in favor of OrderedSet_istotal *)
Definition TOtot {X:hSet} (S : TOSubset X) : istotal (TOSrel S) := pr222 S.

Definition TOSubset_to_OrderedSet {X:hSet} : TOSubset X -> OrderedSet
  := λ S, (carrier_set (pr1 S),,TOSrel S,,TOpartial S),,TOtot S.

Coercion TOSubset_to_OrderedSet : TOSubset >-> OrderedSet.

Notation "s ≤ s'" := (posetRelation (OrderedSet_to_Poset (TOSubset_to_OrderedSet _)) s s') : tosubset.

Notation "s < s'" := (@Poset_lessthan (OrderedSet_to_Poset (TOSubset_to_OrderedSet _)) s s') : tosubset.

Definition TOanti {X:hSet} (S : TOSubset X) : isantisymm (TOSrel S) := pr2 (pr122 S).

Definition TOrefl {X:hSet} (S : TOSubset X) : isrefl (TOSrel S) := pr211 (pr22 S).

Definition TOtrans {X:hSet} (S : TOSubset X) : istrans (TOSrel S).
Proof.
  apply (pr2 S).
Defined.

Definition TOeq_to_refl {X:hSet} (S : TOSubset X) : ∀ s t : carrier_set S, s = t ⇒ posetRelation S s t.
Proof.
  intros s t e. induction e. use TOrefl.
Defined.

Definition TOeq_to_refl_1 {X:hSet} (S : TOSubset X) : ∀ s t : carrier_set S, pr1 s = pr1 t ⇒ s ≤ t.
Proof.
  intros s t e. induction (subtypeEquality_prop e). use TOrefl.
Defined.

Local Lemma le_to_le {X:hSet} {S:TOSubset X} {r s t u:S} :
  (r ≤ t -> pr1 r = pr1 s -> pr1 t = pr1 u -> s ≤ u)%tosubset.
Proof.
  intros le p q. induction (subtypeEquality_prop p). induction (subtypeEquality_prop q). exact le.
Defined.

Local Lemma lt_to_lt {X:hSet} {S:TOSubset X} {r s t u:S} :
  (r < t -> pr1 r = pr1 s -> pr1 t = pr1 u -> s < u)%tosubset.
Proof.
  intros le p q. induction (subtypeEquality_prop p). induction (subtypeEquality_prop q). exact le.
Defined.

Definition tosub_order_compat {X:hSet} {S T : TOSubset X} (le : S ⊆ T) : hProp
  := ∀ s s' : S, s ≤ s' ⇒ subtype_inc le s ≤ subtype_inc le s'.

Definition tosub_le (X:hSet) (S T : TOSubset X) : hProp
  := (∑ le : S ⊆ T, tosub_order_compat le)%prop.

Notation "S ≼ T" := (tosub_le _ S T) (at level 70) : tosubset.

Definition sub_initial {X:hSet} {S : hsubtype X} {T : TOSubset X} (le : S ⊆ T) : hProp
  := ∀ (s t : X) (Ss : S s) (Tt : T t), TOSrel T (t,,Tt) (s,,le s Ss) ⇒ S t.

Definition same_induced_ordering {X:hSet} {S T : TOSubset X} {B : hsubtype X} (BS : B ⊆ S) (BT : B ⊆ T)
  := ∀ x y : B,
             subtype_inc BS x ≤ subtype_inc BS y
                         ⇔
             subtype_inc BT x ≤ subtype_inc BT y.

Definition common_initial {X:hSet} (B : hsubtype X) (S T : TOSubset X) : hProp
  := (∑ (BS : B ⊆ S) (BT : B ⊆ T), sub_initial BS ∧ sub_initial BT ∧ same_induced_ordering BS BT)%prop.

(* the largest initial common ordered subset of S and of T, as the union of all of them *)
Definition max_common_initial {X:hSet} (S T : TOSubset X) : hsubtype X
  := λ x, ∃ (B : hsubtype X), B x ∧ common_initial B S T.

Lemma max_common_initial_is_max {X:hSet} (S T : TOSubset X) (A : hsubtype X) :
  common_initial A S T -> A ⊆ max_common_initial S T.
Proof.
  intros c x Ax. exact (hinhpr (A,,Ax,,c)).
Defined.

Lemma max_common_initial_is_sub {X:hSet} (S T : TOSubset X) :
  max_common_initial S T ⊆ S
  ∧
  max_common_initial S T ⊆ T.
Proof.
  split.
  - intros x m. apply (squash_to_hProp m); intros [B [Bx [BS [_ _]]]]; clear m. exact (BS _ Bx).
  - intros x m. apply (squash_to_hProp m); intros [B [Bx [_ [BT _]]]]; clear m. exact (BT _ Bx).
Defined.

Lemma max_common_initial_is_common_initial {X:hSet} (S T : TOSubset X) :
  common_initial (max_common_initial S T) S T.
Proof.
  exists (pr1 (max_common_initial_is_sub S T)).
  exists (pr2 (max_common_initial_is_sub S T)).
  split.
  { intros x s M Ss le.
    apply (squash_to_hProp M); intros [B [Bx [BS [BT [BSi [BTi BST]]]]]].
    unfold sub_initial in BSi.
    apply hinhpr.
    exists B.
    split.
    + apply (BSi x s Bx Ss). now apply (le_to_le le).
    + exact (BS,,BT,,BSi,,BTi,,BST). }
  split.
  { intros x t M Tt le.
    apply (squash_to_hProp M); intros [B [Bx [BS [BT [BSi [BTi BST]]]]]].
    unfold sub_initial in BSi.
    apply hinhpr.
    exists B.
    split.
    + apply (BTi x t Bx Tt). now apply (le_to_le le).
    + exact (BS,,BT,,BSi,,BTi,,BST). }
  intros x y.
  split.
  { intros le. induction x as [x xm], y as [y ym].
    apply (squash_to_hProp xm); intros [B [Bx [BS [BT [BSi [BTi BST]]]]]].
    apply (squash_to_hProp ym); intros [C [Cy [CS [CT [CSi [CTi CST]]]]]].
    assert (Cx : C x).
    { apply (CSi y x Cy (BS x Bx)). now apply (le_to_le le). }
    assert (Q := pr1 (CST (x,,Cx) (y,,Cy))); simpl in Q.
    assert (E : subtype_inc CS (x,, Cx) ≤ subtype_inc CS (y,, Cy)).
    { now apply (le_to_le le). }
    clear le. now apply (le_to_le (Q E)). }
  { intros le. induction x as [x xm], y as [y ym].
    apply (squash_to_hProp xm); intros [B [Bx [BS [BT [BSi [BTi BST]]]]]].
    apply (squash_to_hProp ym); intros [C [Cy [CS [CT [CSi [CTi CST]]]]]].
    assert (Cx : C x).
    { apply (CTi y x Cy (BT x Bx)). now apply (le_to_le le). }
    assert (Q := pr2 (CST (x,,Cx) (y,,Cy))); simpl in Q.
    assert (E : subtype_inc CT (x,, Cx) ≤ subtype_inc CT (y,, Cy)).
    { now apply (le_to_le le). }
    clear le. now apply (le_to_le (Q E)). }
Defined.

Lemma tosub_fidelity {X:hSet} {S T:TOSubset X} (le : S ≼ T)
      (s s' : S) : s ≤ s' ⇔ subtype_inc (pr1 le) s ≤ subtype_inc (pr1 le) s'.
Proof.
  split.
  { exact (pr2 le s s'). }
  { intro l. apply (squash_to_hProp (TOtot S s s')). intros [c|c].
    - exact c.
    - apply (TOeq_to_refl S s s'). assert (k := pr2 le _ _ c); clear c.
      assert (k' := TOanti T _ _ l k); clear k l.
      apply subtypeEquality_prop. exact (maponpaths pr1 k'). }
Defined.

(** *** Adding a point on top of a totally ordered subset *)

(** We proceed directly.  An indirect way would be to form the corresponding totally ordered
    set, add a point to it, set up an equivalence between that and the union of our subset and
    the new point (assuming decidability of equality), and transport the ordering along the
    equivalence. *)

Definition TOSubset_plus_point_rel {X:hSet} (S:TOSubset X) (z:X) (nSz : ¬ S z) :
  hrel (carrier_set (subtype_plus S z nSz)).
Proof.
  intros [s i] [t j]. unfold subtype_plus in i,j. change hPropset.
  induction i as [Ss|ezs], j as [St|ezt].
  { exact (TOSrel S (s,,Ss) (t,,St)). } { exact htrue. }
  { exact hfalse. }                     { exact htrue. }
Defined.

Lemma isTotalOrder_TOSubset_plus_point {X:hSet} (S:TOSubset X) (z:X) (nSz : ¬ S z) :
  isTotalOrder (TOSubset_plus_point_rel S z nSz).
Proof.
  split.
  { split.
    { split.
      {                         (** transitivity *)
        intros [w Ww] [x Wx] [y [Sy|ezy]] wx xy.
        - induction Ww as [Sw|ezw].
          + induction Wx as [Sx|ezx].
            * change (hProptoType (TOSrel S (w,,Sw) (x,,Sx))) in wx;
              change (hProptoType (TOSrel S (x,,Sx) (y,,Sy))) in xy;
              change (hProptoType (TOSrel S (w,,Sw) (y,,Sy))).
              exact (TOtrans _ _ _ _ wx xy).
            * induction ezx; change empty in xy. exact (fromempty xy).
          + induction ezw. change hfalse.
            induction Wx as [Sx|ezx].
            * change (hProptoType (TOSrel S (x,,Sx) (y,,Sy))) in xy;
                change empty in wx.
              exact wx.
            * induction ezx; change unit in wx; change empty in xy. exact xy.
        - induction ezy. induction Ww as [Sw|ezw].
          + exact tt.
          + induction ezw. exact tt.
      }
      {                         (** reflexivity *)
        intros [x [Sx|ezx]].
        - change (hProptoType (TOSrel S (x,,Sx) (x,,Sx))). apply TOrefl.
        - induction ezx. exact tt. } }
    {                           (** antisymmetry *)
      intros [x [Sx|ezx]] [y [Sy|ezy]] xy yx. apply eqset_to_path.
      - change (hProptoType (TOSrel S (x,,Sx) (y,,Sy))) in xy;
          change (hProptoType (TOSrel S (y,,Sy) (x,,Sx))) in yx.
        apply subtypeEquality_prop; change (x=y).
        exact (maponpaths pr1 (TOanti S _ _ xy yx)).
      - induction ezy. change unit in xy; change empty in yx.
        apply subtypeEquality_prop; change (x=z). exact (fromempty yx).
      - induction ezx. change unit in yx; change empty in xy.
        apply subtypeEquality_prop; change (z=y). exact (fromempty xy).
      - induction ezy, ezx. apply subtypeEquality_prop; change (z=z).
        reflexivity. } }
  {                             (** totality *)
    intros [x [Sx|ezx]] [y [Sy|ezy]].
    - generalize (TOtot S (x,,Sx) (y,,Sy)); apply hinhfun; intros [xy|yx].
      + apply ii1. exact xy.
      + apply ii2. exact yx.
    - induction ezy; change (htrue ∨ hfalse). exact (hinhpr (ii1 tt)).
    - induction ezx; change (hfalse ∨ htrue). exact (hinhpr (ii2 tt)).
    - induction ezy; change (htrue ∨ htrue). exact (hinhpr (ii2 tt)). }
Defined.

Definition TOSubset_plus_point {X:hSet} (S:TOSubset X) (z:X) (nSz : ¬ S z) : TOSubset X
  :=  subtype_plus S z nSz,,
      TOSubset_plus_point_rel S z nSz,,
      isTotalOrder_TOSubset_plus_point S z nSz.

Lemma TOSubset_plus_point_incl {X:hSet} (S:TOSubset X) (z:X) (nSz : ¬ S z) :
  S ⊆ TOSubset_plus_point S z nSz.
Proof.
  apply subtype_plus_incl.
Defined.

Lemma TOSubset_plus_point_le {X:hSet} (S:TOSubset X) (z:X) (nSz : ¬ S z) :
  S ≼ TOSubset_plus_point S z nSz.
Proof.
  use tpair.
  - apply TOSubset_plus_point_incl.
  - intros s t le. exact le.
Defined.

Lemma TOSubset_plus_point_initial {X:hSet} (S:TOSubset X) (z:X) (nSz : ¬ S z) :
  sub_initial (TOSubset_plus_point_incl S z nSz).
Proof.
  intros s t Ss [St|ezt] le.
  - exact St.
  - induction ezt. change empty in le. exact (fromempty le).
Defined.

(** ** Well ordered sets *)

Definition isWellFounded {X : UU} (R : hrel X) : hProp
  := ∀ S : hsubtype X, (∃ x, S x) ⇒ ∃ x:X, S x ∧ ∀ y:X, S y ⇒ R x y.

Definition isWellOrder {X : hSet} (R : hrel X) : hProp := isTotalOrder R ∧ isWellFounded R.

Definition WellOrdering (S:hSet) : hSet := ∑ (R : hrel_set S), isWellOrder R.

Definition WellOrderedSet : UU := (∑ (S:hSet), WellOrdering S)%type.

Definition OrderedSet_to_WellOrderedSet (X : OrderedSet) :
  isWellFounded (posetRelation X) -> WellOrderedSet.
Proof.
  intros wf.
  exists (carrierofposet X).
  exists (posetRelation X).
  split.
  - split.
    + exact (pr221 X).
    + exact (pr2 X).
  - exact wf.
Defined.

Definition WellOrderedSet_to_hSet : WellOrderedSet -> hSet := pr1.

Definition WellOrderedSet_to_OrderedSet : WellOrderedSet -> OrderedSet.
Proof.
  intros [W [R [[po tot] b]]]. exact ((W,,R,,po),,tot).
Defined.

Coercion WellOrderedSet_to_OrderedSet : WellOrderedSet >-> OrderedSet.

Delimit Scope woset with woset.

Definition WOrel (X:WellOrderedSet) : hrel X := pr12 X.

Notation "x ≤ y" := (posetRelation (OrderedSet_to_Poset (WellOrderedSet_to_OrderedSet _)) x y) : woset.

Notation "x < y" := (@Poset_lessthan (OrderedSet_to_Poset (WellOrderedSet_to_OrderedSet _)) x y) : woset.

Definition isInitial {X:OrderedSet} (Y:hsubtype X) : hProp := ∀ (x y : X), Y y ⇒ (x ≤ y ⇒ Y x)%oset.

(** ** Well ordered subsets of a set *)

Definition WOSubset_set (X:hSet) : hSet := ∑ (S:subtype_set X), WellOrdering (carrier_set S).

Definition WOSubset (X:hSet) : UU := WOSubset_set X.

Definition WOSubset_to_subtype {X:hSet} : WOSubset X -> hsubtype X
  := pr1.

Definition WOSrel {X:hSet} (S : WOSubset X)
  : hrel (carrier_set (WOSubset_to_subtype S))
  := pr12 S.

Definition WOStotal {X:hSet} (S : WOSubset X) : isTotalOrder (WOSrel S) := pr122 S.

Definition WOSubset_to_TOSubset {X:hSet} : WOSubset X -> TOSubset X
  := λ S, WOSubset_to_subtype S,, WOSrel S,, WOStotal S.

Coercion WOSubset_to_TOSubset : WOSubset >-> TOSubset.

Definition WOSwo {X:hSet} (S : WOSubset X) : WellOrdering (carrier_set S) := pr2 S.

Definition WOSubset_to_WellOrderedSet {X:hSet} : WOSubset X -> WellOrderedSet.
Proof.
  intros S.
  exists (carrier_set (pr1 S)).
  exact (WOSwo S).
Defined.

Coercion WOSubset_to_WellOrderedSet : WOSubset >-> WellOrderedSet.

Notation "s ≤ s'" := (posetRelation (OrderedSet_to_Poset (TOSubset_to_OrderedSet (WOSubset_to_TOSubset _))) s s') : wosubset.

Notation "s < s'" := (@Poset_lessthan (OrderedSet_to_Poset (TOSubset_to_OrderedSet (WOSubset_to_TOSubset _))) s s') : wosubset.

Lemma WO_lt_anti {X:hSet} (S : WOSubset X) (s : S) : ¬ (s < s).
Proof.
  intros [_ ne]. now use ne.
Defined.

Definition WOS_isWellFounded {X:hSet} (S : WOSubset X) : isWellFounded (WOSrel S)
  := pr222 S.

Lemma wo_lt_to_le {X:hSet} {S : WOSubset X} (s s' : S) : s < s' -> s ≤ s'.
Proof.
  intros lt.
  apply (squash_to_hProp (@OrderedSet_istotal S s s')); intros [c|c].
  - exact c.
  - now apply Poset_lt_to_le.
Defined.

Definition wosub_le (X:hSet) : hrel (WOSubset X)
  := (λ S T : WOSubset X, ∑ (le : S ⊆ T), tosub_order_compat le ∧ sub_initial le)%prop.

Notation "S ≼ T" := (wosub_le _ S T) (at level 70) : wosubset.

Definition wosub_le_inc {X:hSet} {S T : WOSubset X} : S ≼ T -> S ⊆ T := pr1.

Definition wosub_le_comp {X:hSet} {S T : WOSubset X} (le : S ≼ T) : tosub_order_compat (pr1 le)
  := pr12 le.

Definition wosub_le_subi {X:hSet} {S T : WOSubset X} (le : S ≼ T) : sub_initial (pr1 le)
  := pr22 le.

Lemma wosub_le_isrefl {X:hSet} : isrefl (wosub_le X).
Proof.
  intros S.
  use tpair.
  + intros x xinS. exact xinS.
  + split.
    * intros s s' le. exact le.
    * intros s s' Ss Ss' le. exact Ss'.
Defined.

Definition wosub_equal {X:hSet} : hrel (WOSubset X) := λ S T, S ≼ T ∧ T ≼ S.

Notation "S ≣ T" := (wosub_equal S T) (at level 70) : wosubset.

Definition wosub_comparable {X:hSet} : hrel (WOSubset X) := λ S T, S ≼ T ∨ T ≼ S.

Definition isWellFounded_WOSubset_plus_point {X:hSet} (S:WOSubset X) (z:X) (nSz : ¬ S z) :
  LEM ⇒ isWellFounded (TOSrel (TOSubset_plus_point S z nSz)).
Proof.
  intros lem T ne.
  (** T is a nonempty set.  We need to find the smallest element of it *)
  set (S' := TOSubset_plus_point S z nSz).
  assert (S'z := subtype_plus_has_point S z nSz : S' z).
  set (z' := (z,,S'z) : carrier S').
  set (j := TOSubset_plus_point_incl S z nSz). fold S' in j.
  set (jmap := subtype_inc j).
  set (SiT := λ s:S, T (subtype_inc j s)).
  (** Decide whether [S ∩ T] is nonempty: *)
  induction (lem (∃ s, SiT s)) as [q|q].
  - (** ... use the smallest element of SiT *)
    assert (SiTmin := WOS_isWellFounded _ _ q).
    apply (squash_to_hProp SiTmin); clear SiTmin; intros [m [SiTm min]].
    apply hinhpr. set (m' := jmap m). exists m'. split.
    + exact SiTm.
    + intros [t [St|etz]] Tt.
      * change (m ≤ (t,,St)). exact (min (t,,St) Tt).
      * induction etz. change unit. exact tt.
  - (** ... use z *)
    apply hinhpr. exists z'. split.
    + (** T doesn't meet S, so it must contain z *)
      apply (squash_to_hProp ne); clear ne; intros [[t [St|ezt]] Tt].
      * apply fromempty.
        (** S also meets T, so get a contradiction *)
        apply q. apply hinhpr. exists (t,,St).
        change (T (t,, j t St)). exact Tt.
      * induction ezt. unfold z'.
        simple refine (transportf (λ w, T(z,,w)) _ Tt).
        apply proofirrelevance_hProp.
    + (** now show z' is the smallest element of T *)
      intros [t [St|ezt]] Tt.
      * apply fromempty.
        (** t is in S ∩ T, but that's empty *)
        apply q; clear q. apply hinhpr.
        exists (t,,St).
        change (T (t,, j t St)).
        simple refine (transportf (λ w, T(t,,w)) _ Tt).
        apply proofirrelevance_hProp.
      * induction ezt. unfold z'.
        (** now show [z ≤ z], by reflexivity *)
        match goal with |- hProptoType (TOSrel S' (z,,?a) (z,,?b)) => induction (proofirrelevance_hProp _ a b) end.
        exact (TOrefl S' _).
Defined.

Definition WOSubset_plus_point {X:hSet}
           (S:WOSubset X) (z:X) (nSz : ¬ S z) : LEM -> WOSubset X
  := λ lem, subtype_plus S z nSz,,
            TOSrel (TOSubset_plus_point S z nSz),,
            TOtotal (TOSubset_plus_point S z nSz),,
            isWellFounded_WOSubset_plus_point S z nSz lem.

Definition wosub_univalence_map {X:hSet} (S T : WOSubset X) : (S = T) -> (S ≣ T).
Proof.
  intros e. induction e. unfold wosub_equal.
  simple refine ((λ L, dirprodpair L L) _).
  use tpair.
  + intros x s. assumption.
  + split.
    * intros s s' le. assumption.
    * intros s t Ss St le. assumption.
Defined.

Theorem wosub_univalence {X:hSet} (S T : WOSubset X) : (S = T) ≃ (S ≣ T).
Proof.
  simple refine (remakeweq _).
  { unfold wosub_equal.
    intermediate_weq (S ╝ T).
    - apply total2_paths_equiv.
    - intermediate_weq (∑ e : S ≡ T, S ≼ T ∧ T ≼ S)%prop.
      + apply weqbandf.
        * apply hsubtype_univalence.
        * intro p. induction S as [S v], T as [T w]. simpl in p. induction p.
          change (v=w ≃ (S,, v ≼ S,, w ∧ S,, w ≼ S,, v)).
          induction v as [v i], w as [w j].
          intermediate_weq (v=w)%type.
          { apply subtypeInjectivity. change (isPredicate (λ R : hrel (carrier_set S), isWellOrder R)).
            intros R. apply propproperty. }
          apply weqimplimpl.
          { intros p. induction p. split.
            { use tpair.
              { intros s. change (S s → S s). exact (idfun _). }
              { split.
                { intros s s' le. exact le. }
                { intros s t Ss St le. exact St. } } }
            { use tpair.
              { intros s. change (S s → S s). exact (idfun _). }
              { split.
                { intros s s' le. exact le. }
                { intros s t Ss St le. exact St. } } } }
          { simpl. unfold WOSrel. simpl. intros [[a [b _]] [d [e _]]].
            assert (triv : ∏ (f:∏ x : X, S x → S x) (x:carrier_set S), subtype_inc f x = x).
            { intros f s. apply subtypeEquality_prop. reflexivity. }
            apply funextfun; intros s. apply funextfun; intros t.
            apply hPropUnivalence.
            { intros le. assert (q := b s t le). rewrite 2 triv in q. exact q. }
            { intros le. assert (q := e s t le). rewrite 2 triv in q. exact q. } }
          { apply setproperty. }
          { apply propproperty. }
      + apply weqimplimpl.
        { intros k. split ; apply k. }
        { intros c. split.
          { intros x. exact (wosub_le_inc (pr1 c) x,,wosub_le_inc (pr2 c) x). }
          { exact c. } }
        { apply propproperty. }
        { apply propproperty. } }
  { apply wosub_univalence_map. }
  { intros e. induction e. reflexivity. }
Defined.

Lemma wosub_univalence_compute {X:hSet} (S T : WOSubset X) (e : S = T) :
  wosub_univalence S T e = wosub_univalence_map S T e.
Proof.
  reflexivity.
Defined.

Definition wosub_inc {X:hSet} {S T : WOSubset X} : (S ≼ T) -> S -> T.
Proof.
  intros le s. exact (subtype_inc (pr1 le) s).
Defined.

Lemma wosub_fidelity {X:hSet} {S T:WOSubset X} (le : S ≼ T)
      (s s' : S) : s ≤ s' ⇔ wosub_inc le s ≤ wosub_inc le s'.
(** we want this lemma available after showing the union of a chain is totally ordered
   but before showing it has the smallest element condition *)
Proof.
  set (Srel := WOSrel S).
  assert (Stot : istotal Srel).
  { apply (WOSwo S). }
  set (Trel := WOSrel T).
  assert (Tanti : isantisymm Trel).
  { apply (WOSwo T). }
  split.
  { intro l. exact (wosub_le_comp le s s' l). }
  { intro l. apply (squash_to_hProp (Stot s s')).
    change ((s ≤ s') ⨿ (s' ≤ s) → s ≤ s').
    intro c. induction c as [c|c].
    - exact c.
    - induction le as [le [com ini]].
      assert (k := com s' s c).
      assert (k' := Tanti _ _ l k); clear k.
      assert (p : s = s').
      { apply subtypeEquality_prop. exact (maponpaths pr1 k'). }
      induction p. apply (pr2 S). (** refl *) }
Defined.

Local Lemma h1 {X} {S:WOSubset X} {s t u:S} : s = t -> t ≤ u -> s ≤ u.
Proof.
  intros p le. induction p. exact le.
Defined.

Lemma wosub_le_isPartialOrder X : isPartialOrder (wosub_le X).
Proof.
  repeat split.
  - intros S T U i j.
    exists (pr11 (subtype_containment_isPartialOrder X) S T U (pr1 i) (pr1 j)).
    split.
    + intros s s' l. exact (wosub_le_comp j _ _ (wosub_le_comp i _ _ l)).
    + intros s u Ss Uu l.
      change (hProptoType ((u,,Uu) ≤ subtype_inc (pr1 j) (subtype_inc (pr1 i) (s,,Ss)))) in l.
      set (uinT := u ,, wosub_le_subi j s u (pr1 i s Ss) Uu l : T).
      assert (p : subtype_inc (pr1 j) uinT = u,,Uu).
      { now apply subtypeEquality_prop. }
      assert (q := h1 p l : subtype_inc (pr1 j) uinT ≤ subtype_inc (pr1 j) (subtype_inc (pr1 i) (s,,Ss))).
      assert (r := pr2 (wosub_fidelity j _ _) q).
      assert (b := wosub_le_subi i _ _ _ _ r); simpl in b.
      exact b.
  - apply wosub_le_isrefl.
  - intros S T i j. apply (invmap (wosub_univalence _ _)). exact (i,,j).
Defined.

Definition WosubPoset (X:hSet) : Poset.
Proof.
  exists (WOSubset_set X).
  exists (λ S T, S ≼ T).
  exact (wosub_le_isPartialOrder X).
Defined.

Definition wosub_le_smaller {X:hSet} (S T:WOSubset X) : hProp := (S ≼ T) ∧ (∃ t:T, t ∉ S).

Notation "S ≺ T" := (wosub_le_smaller S T) (at level 70) : wosubset.

(** [upto s x] means x is in S and, as an element of S, it is strictly less than s *)
Definition upto {X:hSet} {S:WOSubset X} (s:S) : hsubtype X
  := (λ x, ∑ h:S x, (x,,h) < s)%prop.

Lemma upto_anti {X:hSet} {S:WOSubset X} (s:S) : ¬ (upto s (pr1 s)).
Proof.
  intros [Ss [_ ne]]. use ne; clear ne. now apply subtypeEquality_prop.
Defined.

Lemma upto_eqn {X:hSet} {S T:WOSubset X} (x:X) (Sx : S x) (Tx : T x) :
  S ≼ T -> upto (x,,Sx) = upto (x,,Tx).
Proof.
  intros ST.
  apply (invmap (hsubtype_univalence _ _)).
  intros y.
  split.
  - intros [Sy [le ne]].
    exists (pr1 ST y Sy).
    split.
    + now apply (le_to_le (pr12 ST _ _ le)).
    + intros eq. use ne; clear ne. apply subtypeEquality_prop; change (y=x).
      exact (maponpaths pr1 eq).
  - intros [Ty [le ne]].
    assert (Q := wosub_le_subi ST x y Sx Ty); simpl in Q.
    assert (e : pr1 ST x Sx = Tx).
    { apply propproperty. }
    induction e.
    assert (Sy := Q le : S y); clear Q.
    exists Sy.
    split.
    + apply (pr2 (wosub_fidelity ST (y,, Sy) (x,, Sx))).
      now apply (le_to_le le).
    + intros eq. use ne. apply subtypeEquality_prop; change (y=x).
      exact (maponpaths pr1 eq).
Defined.

Definition isInterval {X:hSet} (S:hsubtype X) (T:WOSubset X) (le : S ⊆ T) :
  LEM -> sub_initial le -> T ⊈ S -> ∃ t:T, S ≡ upto t.
Proof.
  intros lem ini ne.
  set (R := WOSrel T).
  assert (min := WOS_isWellFounded T).
  set (U := (λ t:T, t ∉ S) : hsubtype (carrier T)). (** complement of S in T *)
  assert (neU : nonempty (carrier U)).
  { apply (squash_to_hProp ne); intros [x [Tx nSx]]. apply hinhpr. exact ((x,,Tx),,nSx). }
  clear ne. assert (minU := min U neU); clear min neU.
  apply (squash_to_hProp minU); clear minU; intros [u [Uu minu]].
  (** minu says that u is the smallest element of T not in S *)
  apply hinhpr. exists u. intro y. split.
  - intro Sy. change (∑ Ty : T y, y,,Ty < u).
    exists (le y Sy). apply (@nle_to_gt T _ _).
    intro ules. use Uu. exact (ini _ _ _ _ ules).
  - intro yltu. induction yltu as [yinT yltu].
    (** Goal : [S y].  We know y is smaller than the smallest element of T not in S,
       so at best, constructively, we know [¬ ¬ (S y)].  So prove it by contradiction. *)
    apply (proof_by_contradiction lem).
    intro bc. use ((@gt_to_nle T _ _) yltu). now use minu.
Defined.

(** ** The union of a chain of totally ordered subsets *)

Definition is_wosubset_chain {X : hSet} {I : UU} (S : I → WOSubset X)
  := ∀ i j : I, wosub_comparable (S i) (S j).

Lemma common_index {X : hSet} {I : UU} {S : I → WOSubset X}
      (chain : is_wosubset_chain S) (i : I) (x : carrier_set (⋃ (λ i, S i))) :
   ∃ j, S i ≼ S j ∧ S j (pr1 x).
Proof.
  induction x as [x xinU]. apply (squash_to_hProp xinU); intros [k xinSk].
  change (∃ j : I, S i ≼ S j ∧ S j x).
  apply (squash_to_hProp (chain i k)). intros c. apply hinhpr. induction c as [c|c].
  - exists k. split.
    + exact c.
    + exact xinSk.
  - exists i. split.
    + apply wosub_le_isrefl.
    + exact (pr1 c x xinSk).
Defined.

Lemma common_index2 {X : hSet} {I : UU} {S : I → WOSubset X}
      (chain : is_wosubset_chain S) (x y : carrier_set (⋃ (λ i, S i))) :
   ∃ i, S i (pr1 x) ∧ S i (pr1 y).
Proof.
  induction x as [x j], y as [y k]. change (∃ i, S i x ∧ S i y).
  apply (squash_to_hProp j). clear j. intros [j s].
  apply (squash_to_hProp k). clear k. intros [k t].
  apply (squash_to_hProp (chain j k)). clear chain. intros [c|c].
  - apply hinhpr. exists k. split.
    + exact (pr1 c x s).
    + exact t.
  - apply hinhpr. exists j. split.
    + exact s.
    + exact (pr1 c y t).
Defined.

Lemma common_index3 {X : hSet} {I : UU} {S : I → WOSubset X}
      (chain : is_wosubset_chain S) (x y z : carrier_set (⋃ (λ i, S i))) :
   ∃ i, S i (pr1 x) ∧ S i (pr1 y) ∧ S i (pr1 z).
Proof.
  induction x as [x j], y as [y k], z as [z l]. change (∃ i, S i x ∧ S i y ∧ S i z).
  apply (squash_to_hProp j). clear j. intros [j s].
  apply (squash_to_hProp k). clear k. intros [k t].
  apply (squash_to_hProp l). clear l. intros [l u].
  apply (squash_to_hProp (chain j k)). intros [c|c].
  - apply (squash_to_hProp (chain k l)). clear chain. intros [d|d].
    + apply hinhpr. exists l. repeat split.
      * exact (pr1 d x (pr1 c x s)).
      * exact (pr1 d y t).
      * exact u.
    + apply hinhpr. exists k. repeat split.
      * exact (pr1 c x s).
      * exact t.
      * exact (pr1 d z u).
  - apply (squash_to_hProp (chain j l)). clear chain. intros [d|d].
    + apply hinhpr. exists l. repeat split.
      * exact (pr1 d x s).
      * exact (pr1 d y (pr1 c y t)).
      * exact u.
    + apply hinhpr. exists j. repeat split.
      * exact s.
      * exact (pr1 c y t).
      * exact (pr1 d z u).
Defined.

Lemma chain_union_prelim_eq0 {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S)
           (x y : X) (i j: I) (xi : S i x) (xj : S j x) (yi : S i y) (yj : S j y) :
  WOSrel (S i) (x ,, xi) (y ,, yi) = WOSrel (S j) (x ,, xj) (y ,, yj).
Proof.
  apply weqlogeq.
  apply (squash_to_hProp (chain i j)). intros [c|c].
  - split.
    + intro l. assert (q := wosub_le_comp c _ _ l); clear l. now apply (le_to_le q).
    + intro l. apply (pr2 ((wosub_fidelity c) (x,,xi) (y,,yi))).
      now apply (@le_to_le X (S j) _ _ _ _ l).
  - split.
    + intro l. apply (pr2 ((wosub_fidelity c) (x,,xj) (y,,yj))).
      now apply (@le_to_le X (S i) _ _ _ _ l).
    + intro l. assert (q := wosub_le_comp c _ _ l); clear l. now apply (le_to_le q).
Defined.

Definition chain_union_rel {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S) :
  hrel (carrier_set (⋃ (λ i, S i))).
Proof.
  intros x y.
  change (hPropset). simple refine (squash_to_hSet _ _ (common_index2 chain x y)).
  - intros [i [s t]]. exact (WOSrel (S i) (pr1 x,,s) (pr1 y,,t)).
  - intros i j. now apply chain_union_prelim_eq0.
Defined.

Definition chain_union_rel_eqn {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S)
           (x y : carrier_set (⋃ (λ i, S i)))
           i (s : S i (pr1 x)) (t : S i (pr1 y)) :
  chain_union_rel chain x y = WOSrel (S i) (pr1 x,,s) (pr1 y,,t).
Proof.
  unfold chain_union_rel. generalize (common_index2 chain x y); intro h.
  assert (e : hinhpr (i,,s,,t) = h).
  { apply propproperty. }
  now induction e.
Defined.

Lemma chain_union_rel_istrans {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S) :
  istrans (chain_union_rel chain).
Proof.
  intros x y z l m.
  apply (squash_to_hProp (common_index3 chain x y z)); intros [i [r [s t]]].
  assert (p := chain_union_rel_eqn chain x y i r s).
  assert (q := chain_union_rel_eqn chain y z i s t).
  assert (e := chain_union_rel_eqn chain x z i r t).
  rewrite p in l; clear p.
  rewrite q in m; clear q.
  rewrite e; clear e.
  assert (tot : istrans (WOSrel (S i))).
  { apply (pr2 (S i)). }
  exact (tot _ _ _ l m).
Defined.

Lemma chain_union_rel_isrefl {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S) :
  isrefl (chain_union_rel chain).
Proof.
  intros x. apply (squash_to_hProp (pr2 x)). intros [i r].
  assert (p := chain_union_rel_eqn chain x x i r r). rewrite p; clear p. apply (pr2 (S i)).
Defined.

Lemma chain_union_rel_isantisymm {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S) :
  isantisymm (chain_union_rel chain).
Proof.
  intros x y l m.
  change (x=y)%set.
  apply (squash_to_hProp (common_index2 chain x y)); intros [i [r s]].
  apply subtypeEquality_prop.
  assert (p := chain_union_rel_eqn chain x y i r s). rewrite p in l; clear p.
  assert (q := chain_union_rel_eqn chain y x i s r). rewrite q in m; clear q.
  assert (anti : isantisymm (WOSrel (S i))).
  { apply (pr2 (S i)). }
  assert (b := anti _ _ l m); clear anti l m.
  exact (maponpaths pr1 b).
Defined.

Lemma chain_union_rel_istotal {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S) :
  istotal (chain_union_rel chain).
Proof.
  intros x y.
  apply (squash_to_hProp (common_index2 chain x y)); intros [i [r s]].
  assert (p := chain_union_rel_eqn chain x y i r s). rewrite p; clear p.
  assert (p := chain_union_rel_eqn chain y x i s r). rewrite p; clear p.
  apply (pr2 (S i)).
Defined.

Lemma chain_union_rel_isTotalOrder {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S) :
  isTotalOrder (chain_union_rel chain).
Proof.
  repeat split.
  - apply chain_union_rel_istrans.
  - apply chain_union_rel_isrefl.
  - apply chain_union_rel_isantisymm.
  - apply chain_union_rel_istotal.
Defined.

Definition chain_union_TOSubset {X : hSet} {I : UU} {S : I → WOSubset X}
           (Schain : is_wosubset_chain S) : TOSubset X.
Proof.
  exists (⋃ S).
  exists (chain_union_rel Schain).
  repeat split.
  - apply chain_union_rel_istrans.
  - apply chain_union_rel_isrefl.
  - apply chain_union_rel_isantisymm.
  - apply chain_union_rel_istotal.
Defined.

Notation "⋃ chain" := (chain_union_TOSubset chain) (at level 100, no associativity) : tosubset.

(** ** The union of a chain of well ordered subsets *)

Lemma chain_union_tosub_le {X : hSet} {I : UU} {S : I → WOSubset X}
      (Schain : is_wosubset_chain S) (i:I)
      (inc := subtype_inc (subtype_union_containedIn S i)) :
  ( S i ≼ ⋃ Schain ) % tosubset.
Proof.
  exists (subtype_union_containedIn S i).
  intros s s' j.
  set (u := subtype_inc (λ x J, hinhpr (i,, J)) s : ⋃ Schain).
  set (u':= subtype_inc (λ x J, hinhpr (i,, J)) s': ⋃ Schain).
  change (chain_union_rel Schain u u').
  assert (q := chain_union_rel_eqn Schain u u' i (pr2 s) (pr2 s')).
  rewrite q; clear q. exact j.
Defined.

Lemma chain_union_rel_initial {X : hSet} {I : UU} {S : I → WOSubset X}
      (Schain : is_wosubset_chain S) (i:I)
      (inc := subtype_inc (subtype_union_containedIn S i)) :
    (∀ s:S i, ∀ t:⋃ Schain, t ≤ inc s ⇒ t ∈ S i)%tosubset.
Proof.
  intros s t le.
  apply (squash_to_hProp (common_index Schain i t)).
  intros [j [[ij [com ini]] tinSj]]. set (t' := (pr1 t,,tinSj) : S j). unfold sub_initial in ini.
  assert (K := ini (pr1 s) (pr1 t') (pr2 s) (pr2 t')); simpl in K. change (t' ≤ subtype_inc ij s → t ∈ S i) in K.
  apply K; clear K. unfold tosub_order_compat in com.
  apply (pr2 (tosub_fidelity (chain_union_tosub_le Schain j) t' (subtype_inc ij s))).
  clear com ini.
  assert (p : t = subtype_inc (pr1 (chain_union_tosub_le _ j)) t').
  { now apply subtypeEquality_prop. }
  induction p.
  assert (q : inc s = subtype_inc (pr1 (chain_union_tosub_le Schain j)) (subtype_inc ij s)).
  { now apply subtypeEquality_prop. }
  induction q.
  exact le.
Defined.

Lemma chain_union_rel_isWellFounded {X : hSet} {I : UU} {S : I → WOSubset X}
           (chain : is_wosubset_chain S) :
  isWellFounded (chain_union_rel chain).
Proof.
  intros T t'.
  apply (squash_to_hProp t'); clear t'; intros [[x i] xinT].
  apply (squash_to_hProp i); intros [j xinSj].
  induction (ishinh_irrel ( j ,, xinSj ) i).
  (** T' is the intersection of T with S j *)
  set (T' := (λ s, T (subtype_inc (subtype_union_containedIn S j) s))).
  assert (t' := hinhpr ((x,,xinSj),,xinT) : ∥ carrier T' ∥); clear x xinSj xinT.
  assert (min := WOS_isWellFounded (S j) T' t'); clear t'.
  apply (squash_to_hProp min); clear min; intros [t0 [t0inT' t0min]].
  (** t0 is the minimal element of T' *)
  set (t0' := subtype_inc (subtype_union_containedIn S j) t0).
  apply hinhpr. exists t0'. split.
  - exact t0inT'.
  - intros t tinT.
    (** Now show any other element t of T is at least as big as t0'.
        For that purpose, we may assume t ≤ t0'. *)
    apply (hdisj_impl_2 (chain_union_rel_istotal chain _ _)); intro tle.
    set (q := chain_union_rel_initial chain j t0 t tle).
    set (t' := (pr1 t,,q) : S j).
    assert (E : subtype_inc (subtype_union_containedIn S j) t' = t).
    { now apply subtypeEquality_prop. }
    rewrite <- E. unfold t0'.
    apply (pr2 (chain_union_tosub_le chain j) t0 t'). apply (t0min t').
    unfold T'. rewrite E. exact tinT.
Defined.

Lemma chain_union_WOSubset {X:hSet} {I:UU} {S : I -> WOSubset X} (Schain : is_wosubset_chain S)
  : WOSubset X.
Proof.
  exists (⋃ Schain). exists (chain_union_rel Schain).
  repeat split.
  - apply chain_union_rel_istrans.
  - apply chain_union_rel_isrefl.
  - apply chain_union_rel_isantisymm.
  - apply chain_union_rel_istotal.
  - apply chain_union_rel_isWellFounded.
Defined.

Notation "⋃ chain" := (chain_union_WOSubset chain) (at level 100, no associativity) : wosubset.

Lemma chain_union_le {X:hSet} {I:UU} (S : I -> WOSubset X) (Schain : is_wosubset_chain S) :
  ∀ i, S i ≼ ⋃ Schain.
Proof.
  intros i. exists (subtype_union_containedIn S i). split.
  * exact (pr2 (chain_union_tosub_le _ i)).
  * intros s t Ss Tt.
    exact (chain_union_rel_initial Schain i (s,,Ss) (t,,Tt)).
Defined.

Definition proper_subtypes_set (X:UU) : hSet := ∑ S : subtype_set X, ∃ x, ¬ (S x).

(** the interval up to c, as a proper subset of X *)
Definition upto' {X:hSet} {C:WOSubset X} (c:C) : proper_subtypes_set X.
Proof.
  exists (upto c). apply hinhpr. exists (pr1 c). intro n.
  simpl in n. induction n as [n o]. apply o; clear o.
  now apply subtypeEquality_prop.
Defined.

(** ** Choice functions *)

(** A choice function provides an element not in each proper subset.  *)

Definition choice_fun (X:hSet) := ∏ S : proper_subtypes_set X, ∑ x : X, ¬ pr1 S x.

Lemma AC_to_choice_fun (X:hSet) : AxiomOfChoice ⇒ ∥ choice_fun X ∥.
Proof.
  intros ac.
  exact (squash_to_hProp (ac (proper_subtypes_set X)
                             (λ S, ∑ x, ¬ (pr1 S x)) pr2)
                         hinhpr).
Defined.

(** Given a choice function g, we single out well ordered subsets C of X that
    follow the choice functions advice when constructed by adding one element at
    a time to the top.  We may say that C is "guided" by g. *)

Definition is_guided_WOSubset {X:hSet} (g : choice_fun X) (C : WOSubset X) : hProp
  := ∀ c:C, pr1 c = pr1 (g (upto' c)).

Lemma upto'_eqn {X:hSet} (g : choice_fun X) (C D : WOSubset X) (j : C ≼ D)
      (c : C) (d : D) :
  pr1 (subtype_inc (pr1 j) c) = pr1 d ->
  pr1 (g (upto' c)) = pr1 (g (upto' d)).
Proof.
  intros p. assert (e' : upto' c = upto' d).
  { apply subtypeEquality_prop. change (upto c = upto d).
    assert (q : subtype_inc (pr1 j) c = d).
    { now apply subtypeEquality_prop. }
    clear p. induction q.
    now apply upto_eqn. }
  now induction e'.
Defined.

Definition Guided_WOSubset {X:hSet} (g : choice_fun X) := (∑ C, is_guided_WOSubset g C)%type.

Definition guidedFamily {X:hSet} (g : choice_fun X) : Guided_WOSubset g -> WOSubset X
  := pr1.

Coercion guidedFamily : Guided_WOSubset >-> WOSubset.

(** ** The guided well ordered subsets form a chain *)

Lemma guided_WOSubset_total {X:hSet} (g : choice_fun X) :
  LEM -> is_wosubset_chain (guidedFamily g).
Proof.
  intros lem [C gC] [D gD].
  set (W := max_common_initial C D).
  assert (Q := max_common_initial_is_common_initial C D).
  induction Q as [WC [WD [WCi [WDi WCD]]]]; fold W in WC, WD, WCi, WDi.
  assert (E : W ≡ C ∨ W ≡ D).
  { apply (proof_by_contradiction lem); intro h.
    assert (k := fromnegcoprod_prop h); clear h; induction k as [nc nd].
    assert (nCW : C ⊈ W).
    { use subtype_notEqual_containedIn.
      - exact WC.
      - now apply subtype_notEqual_from_negEqual. }
    assert (nDW : D ⊈ W).
    { use subtype_notEqual_containedIn.
      - exact WD.
      - now apply subtype_notEqual_from_negEqual. }
    assert (p : ∃ t : C, W ≡ upto t). { now use isInterval. }
    assert (q : ∃ t : D, W ≡ upto t). { now use isInterval. }
    change hfalse.
    apply (squash_to_hProp p); clear p; intros [c cE].
    apply (squash_to_hProp q); clear q; intros [d dE].
    assert (ce : W = upto c).
    { now apply (invmap (hsubtype_univalence _ _)). }
    assert (de : W = upto d).
    { now apply (invmap (hsubtype_univalence _ _)). }
    assert (cd := !ce @ de : upto c = upto d).
    assert (cd' : upto' c = upto' d).
    { now apply subtypeEquality_prop. }
    assert (p := gC c); simpl in p.
    assert (q := gD d); simpl in q.
    unfold choice_fun in g.
    assert (cd1 : pr1 c = pr1 d).
    { simple refine (p @ _ @ !q). now induction cd'. }
    clear cd'.
    assert (nWc : ¬ W (pr1 c)).
    { intros Wc. exact (upto_anti _ (pr1 (cE (pr1 c)) Wc)). }
    set (W' := subtype_plus W (pr1 c) nWc).
    assert (j := subtype_plus_incl W (pr1 c) nWc : W ⊆ W').
    assert (W'c := subtype_plus_has_point W (pr1 c) nWc : W' (pr1 c)).
    assert (W'd := transportf W' cd1 W'c : W' (pr1 d)).
    assert (ci : common_initial W' C D).
    { assert (W'C := subtype_plus_in nWc WC (pr2 c));
        assert (W'D := subtype_plus_in nWc WD (transportb (λ x : X, D x) cd1 (pr2 d)));
        fold W' in W'C, W'D.
      exists W'C, W'D.
      assert (cmax : ∏ (v : carrier W') (W'c : W' (pr1 c)),
                     subtype_inc W'C v ≤ subtype_inc W'C (pr1 c,,W'c)).
      { intros v W'c'. assert (e : c = subtype_inc W'C (pr1 c,, W'c')).
        { now apply subtypeEquality_prop. }
        induction e. clear W'c'. induction v as [v [Wv|k]].
        - assert (L := pr1 (cE v) Wv).
          induction L as [Cv lt].
          now apply (le_to_le (pr1 lt)).
        - use (TOeq_to_refl C). now apply subtypeEquality_prop. }
      assert (cmax' : ∏ (w : carrier W) (W'c : W' (pr1 c)),
                     subtype_inc W'C (subtype_inc j w) < subtype_inc W'C (pr1 c,,W'c)).
      { intros w W'c'. assert (e : c = subtype_inc W'C (pr1 c,, W'c')).
        { now apply subtypeEquality_prop. }
        induction e. clear W'c'. induction w as [v Wv].
        assert (L := pr1 (cE v) Wv). unfold upto,lt in L.
        now apply (lt_to_lt (pr2 L)). }
      assert (dmax : ∏ (v : carrier W') (W'd : W' (pr1 d)),
                     subtype_inc W'D v ≤ subtype_inc W'D (pr1 d,,W'd)).
      { intros v W'd'. assert (e : d = subtype_inc W'D (pr1 d,, W'd')).
        { now apply subtypeEquality_prop. }
        induction e. clear W'd'. induction v as [v [Wv|k]].
        - assert (L := pr1 (dE v) Wv). unfold upto,lt in L.
          apply wo_lt_to_le. now apply (lt_to_lt (pr2 L)).
        - use (TOeq_to_refl D). apply subtypeEquality_prop. simpl. exact (!k @ cd1). }
      assert (dmax' : ∏ (w : carrier W) (W'd : W' (pr1 d)),
                     subtype_inc W'D (subtype_inc j w) < subtype_inc W'D (pr1 d,,W'd)).
      { intros w W'd'. assert (e : d = subtype_inc W'D (pr1 d,, W'd')).
        { now apply subtypeEquality_prop. }
        induction e. clear W'd'. induction w as [v Wv].
        assert (L := pr1 (dE v) Wv). unfold upto,lt in L.
        now apply (lt_to_lt (pr2 L)). }
      split.
      { intros w' c' [Ww'|e] Cc' le.
        - apply ii1. apply (WCi w' c' Ww' Cc'). now apply (le_to_le le).
        - induction e.
          induction (lem (pr1 c = c')) as [e|ne].
          + induction e. exact W'c.
          + use j. rewrite ce. exists Cc'. unfold lt.
            split.
            * now apply (le_to_le le).
            * intros eq. use ne. apply pathsinv0. exact (maponpaths pr1 eq). }
      split.
      { intros w' d' [Ww'|e] Dd' le.
        - apply ii1. apply (WDi w' d' Ww' Dd'). now apply (le_to_le le).
        - induction e.
          induction (lem (pr1 d = d')) as [e|ne].
          + induction e. exact W'd.
          + use j. rewrite de. exists Dd'. unfold lt.
            split.
            * now apply (le_to_le le).
            * intros eq. use ne. apply pathsinv0. exact (maponpaths pr1 eq). }
      {
        intros [v [Wv|Ev]] [w [Ww|Ew]].
        - assert (Q := WCD (v,,Wv) (w,,Ww)).
          change (hProptoType (
                      (subtype_inc WC (v,, Wv) ≤ subtype_inc WC (w,, Ww))
                        ⇔
                        (subtype_inc WD (v,, Wv) ≤ subtype_inc WD (w,, Ww))
                    )%tosubset) in Q.
          assert (e : subtype_inc W'C (v,, ii1 Wv) = subtype_inc WC (v,, Wv)).
          { now apply subtypeEquality_prop. }
          induction e.
          assert (e : subtype_inc W'C (w,, ii1 Ww) = subtype_inc WC (w,, Ww)).
          { now apply subtypeEquality_prop. }
          induction e.
          assert (e : subtype_inc W'D (v,, ii1 Wv) = subtype_inc WD (v,, Wv)).
          { now apply subtypeEquality_prop. }
          induction e.
          assert (e : subtype_inc W'D (w,, ii1 Ww) = subtype_inc WD (w,, Ww)).
          { now apply subtypeEquality_prop. }
          induction e.
          exact Q.
        - induction Ew. apply logeq_if_both_true.
          + apply cmax.
          + induction (!cd1). apply dmax.
        - induction Ev. apply logeq_if_both_false.
          + assert (Q := cmax' (w,,Ww) W'c).
            apply (@gt_to_nle C _ _).
            now apply (lt_to_lt Q).
          + assert (Q := dmax' (w,,Ww) W'd). unfold lt in Q.
            apply (@gt_to_nle D _ _).
            now apply (lt_to_lt Q).
        - induction Ew. apply logeq_if_both_true ; now use TOeq_to_refl_1. } }
    assert (K := max_common_initial_is_max C D W' ci); fold W in K.
    assert (Wc : W (pr1 c)).
    { exact (K (pr1 c) W'c). }
    assert (L := pr1 (cE (pr1 c)) Wc). induction L as [Cc Q].
    assert (M : c < c).
    { now apply (lt_to_lt Q). }
    clear Q.
    use (Poset_lt_to_ne _ _ M); clear M.
    reflexivity. }
  change (wosub_comparable C D). unfold wosub_comparable.
  apply (squash_to_hProp E); clear E; intros E. apply hinhpr.
  Set Printing Coercions.
  induction E as [eWC|eWD].
  - apply ii1.
    assert (e : W = C).
    { now apply hsubtype_univalence. }
    unfold W in *. clear W.
    induction (!e); clear e.
    use tpair.
    { exact WD. }
    split.
    { intros x y le. apply (pr1 (WCD x y)). now apply (le_to_le le). }
    exact WDi.
  - apply ii2.
    assert (e : W = D).
    { now apply hsubtype_univalence. }
    unfold W in *. clear W.
    induction (!e); clear e.
    use tpair.
    { exact WC. }
    split.
    { intros x y le. apply (pr2 (WCD x y)). now apply (le_to_le le). }
    exact WCi.
  Unset Printing Coercions.
Defined.

(** ** The proof of the well ordering theorem of Zermelo *)

Theorem ZermeloWellOrdering (X:hSet) : AxiomOfChoice ⇒ ∃ R : hrel X, isWellOrder R.
(** see http://www.math.illinois.edu/~dan/ShortProofs/WellOrdering.pdf *)
Proof.
  intros ac. assert (lem := AC_to_LEM ac).
  (** a choice function g allows us to single out the "guided" well ordered subsets of X *)
  apply (squash_to_hProp (AC_to_choice_fun X ac)); intro g.
  set (S := guidedFamily g).
  set (Schain := guided_WOSubset_total g lem).
  (** we form the union, W, of all the guided (well ordered) subsets of X *)
  set (W := ⋃ Schain).
  (** we show W itself is guided, so W is the biggest guided subset of X *)
  assert (Wguided : is_guided_WOSubset g W).
  { intros [w Ww]. apply (squash_to_hProp Ww); intros [C Cw].
    change (hProptoType (C w)) in Cw. simpl.
    assert (Q := pr2 C (w,,Cw)); simpl in Q.
    simple refine (Q @ _); clear Q.
    assert (CW := chain_union_le S Schain C : C ≼ W).
    use upto'_eqn.
    - exact CW.
    - reflexivity. }
  (** now we prove W is all of X *)
  assert (all : ∀ x, W x).
  { (** ... for if not, we can add a guided element and get a bigger guided subset *)
    apply (proof_by_contradiction lem); intro n.
    (** it's not constructive to get an element not in W: *)
    assert (Q := negforall_to_existsneg _ lem n); clear n.
    change hfalse.
    (** zn is the guided element not in W: *)
    set (znW := g (pr1 W,,Q) : ∑ z : X, ¬ pr1 W z).
    set (z := pr1 znW).
    set (nWz := pr2 znW : ¬ pr1 W z).
    (** make a larger well ordered subset of X by appending z to the top of W *)
    set (W' := WOSubset_plus_point W z nWz lem).
    assert (W'z := subtype_plus_has_point W z nWz : W' z).
    set (j := TOSubset_plus_point_incl W z nWz : W ⊆ W').
    set (jmap := subtype_inc j).
    assert (W'guided : is_guided_WOSubset g W').
    { unfold is_guided_WOSubset.
      intros [x W'x].
      induction W'x as [Wx|ezx].
      - assert (x_guided := Wguided (x,,Wx)).
        change (x = pr1 (g (@upto' X W (x,, Wx))))%type in x_guided.
        simple refine (x_guided @ _); clear x_guided.
        use upto'_eqn.
        + (** show W ≼ W'; abstract later *)
          assert (WW' := TOSubset_plus_point_le W z nWz).
          induction WW' as [WW' comp].
          exists WW'.
          split.
          { exact comp. }
          { intros w w' Ww W'w' le.
            simple refine (TOSubset_plus_point_initial W z nWz w w' Ww W'w' _).
            now apply (le_to_le le). }
        + reflexivity.
      - induction ezx.
        change (pr1 (g (pr1 W,, Q)) = pr1 (g (@upto' X W' (z,, ii2 (idpath z))))).
        apply (maponpaths (λ E, pr1 (g E))).
        { apply subtypeEquality_prop. apply (invmap (hsubtype_univalence _ _)).
          intros y.
          change (W y ⇔ @upto X W' (z,, ii2 (idpath z)) y).
          split.
          - intros Wy.
            (** show that the element y in W is less than z *)
            exists (j y Wy).
            split.
            + reflexivity.
            + intros ne. use nWz.
              assert (ne' := maponpaths pr1 ne : y = z); clear ne.
              induction ne'.
              exact Wy.
          - (** show that if y in W' is less than z, then it's in W *)
            intros [[Wy|ezy] yz].
            + exact Wy.         (** it was in W, anyway *)
            + induction ezy.    (** y = x, and we know z<z *)
              apply fromempty. unfold lt,hneg in yz.
              assert (K := Poset_lt_to_ne _ _ yz); clear yz.
              use K; clear K.
              now apply subtypeEquality_prop. } }
    assert (W'W := chain_union_le S Schain (W',,W'guided) : W' ≼ W).
    assert (K := pr2 (subtype_inc (pr1 W'W) (z,,W'z)) : W z).
    exact (nWz K).
    }
  clear Wguided.
  apply hinhpr.
  induction W as [W R'].
  change (∏ x : X, W x)%type in all.
  change (WellOrdering X).
  assert (e : X = carrier_set W).
  { apply (invmap (hSet_univalence _ _)). apply invweq. apply weqpr1.
    intros x.
    simpl in all.
    apply iscontraprop1.
    - apply propproperty.
    - apply all. }
  induction e. exact R'.
Defined.

Corollary multiZermeloWellOrdering (I:hSet) (X:I->hSet) :
  AxiomOfChoice ⇒ ∥ ∏ i, ∑ R : hrel (X i), isWellOrder R ∥ %type.
Proof.
  intros ac. use ac. intros i. apply ZermeloWellOrdering. exact ac.
Defined.

(** ** Well ordered sets *)

Local Open Scope woset.

Lemma isaprop_theSmallest {X : hSet}
      (R : hrel X) (total : isTotalOrder R) (S : hsubtype X) :
  isaprop (∑ s:X, S s ∧ ∀ t:X, S t ⇒ R s t).
Proof.
  induction total as [[po anti] tot].
  apply invproofirrelevance; intros s t. apply subtypeEquality_prop.
  induction s as [x i], t as [y j], i as [I i], j as [J j]. change (x=y)%set.
  apply (squash_to_hProp (tot x y)); intros [c|c].
  { apply anti. { exact c. } { exact (j x I). } }
  { apply anti. { exact (i y J). } { exact c. } }
Defined.

Definition WO_isTotalOrder (X : WellOrderedSet) : isTotalOrder (WOrel X) := pr122 X.

Definition WO_isPartialOrder (X : WellOrderedSet) : isPartialOrder (WOrel X) := pr1 (WO_isTotalOrder X).

Definition WO_istotal (X : WellOrderedSet) : istotal (WOrel X) := pr2 (WO_isTotalOrder X).

Definition WO_isWellFounded (X : WellOrderedSet) : isWellFounded (WOrel X) := pr222 X.

Definition theSmallest {X : WellOrderedSet} {S : hsubtype X} (ne : ∃ s, S s)
  := hProppair
       (∑ s:X, S s ∧ ∀ t:X, S t ⇒ WOrel X s t)
       (isaprop_theSmallest _ (WO_isTotalOrder X) S).

(** actually get the smallest element: *)
Lemma WO_theSmallest {X : WellOrderedSet} {S : hsubtype X} (ne : ∃ s, S s) : theSmallest ne.
Proof.
  apply (squash_to_hProp (WO_isWellFounded X S ne)). intro c. exact c.
Defined.

Lemma WO_theUniqueSmallest {X : WellOrderedSet} (S : hsubtype X) :
 (∃ s, S s) ⇒ ∃! s:X, S s ∧ ∀ t:X, S t ⇒ s ≤ t.
Proof.
  intros ne. apply iscontraprop1.
  - apply isaprop_theSmallest. apply WO_isTotalOrder.
  - exact (WO_theSmallest ne).
Defined.

Definition is_WellOrderedSet_map {X Y : WellOrderedSet} (f : X -> Y) : hProp :=
  hProppair
    (isaposetmorphism (f : (X : Poset) -> (Y : Poset)))
    (isaprop_isaposetmorphism _).

Definition WellOrderedSet_map (X Y : WellOrderedSet) := (∑ f : X → Y, is_WellOrderedSet_map f)%type.

Definition WellOrderedSet_map_to_function {X Y : WellOrderedSet} (f : WellOrderedSet_map X Y) : X -> Y := pr1 f.

Coercion WellOrderedSet_map_to_function : WellOrderedSet_map >-> Funclass.

Lemma WellOrderedSet_map_lt_inv {X Y : WellOrderedSet} (f : WellOrderedSet_map X Y) (x x':X) :
  (f x < f x' -> x < x')%woset.
Proof.
  intros lt.
  use nle_to_gt.
  intros le.
  use (Poset_lt_to_nle lt).
  now use (pr2 f).
Defined.

Definition WellOrderedSet_iso (X Y : WellOrderedSet) := (∑ f : X ≃ Y, is_WellOrderedSet_map f)%type.

Notation "X ≅ Y" := (WellOrderedSet_iso X Y) : woset.

Definition WellOrderedSet_iso_to_map {X Y : WellOrderedSet} : X ≅ Y -> WellOrderedSet_map X Y
  := λ f, pr1weq (pr1 f) ,, pr2 f.

Coercion WellOrderedSet_iso_to_map : WellOrderedSet_iso >-> WellOrderedSet_map.

Definition WellOrderedSet_iso_to_weq {X Y : WellOrderedSet} : X ≅ Y -> X ≃ Y := pr1.

Coercion WellOrderedSet_iso_to_weq : WellOrderedSet_iso >-> weq.

Lemma WellOrderedSet_iso_lt_inv {X Y : WellOrderedSet} (f : X ≅ Y) {y y':Y} :
  (y < y' -> invmap f y < invmap f y')%woset.
Proof.
  intros lt.
  use nle_to_gt.
  intros le.
  assert (le' := pr2 f _ _ le : f (invmap f y') ≤ f (invmap f y)); clear le.
  assert (p : f (invmap f y) = y).
  { apply homotweqinvweq. }
  assert (p' : f (invmap f y') = y').
  { apply homotweqinvweq. }
  induction (!p), (!p'); clear p p'.
  exact (Poset_lt_to_nle lt le').
Defined.

Definition WellOrderedSet_univalence_map (X Y : WellOrderedSet) : (X = Y → X ≅ Y)%type.
Proof.
  intros []. exists (idweq X). intros x y le. exact le.
Defined.

Lemma WellOrderedSet_univalence (X Y : WellOrderedSet) : (X = Y ≃ X ≅ Y)%type.
Proof.
  use (remakeweq (g := WellOrderedSet_univalence_map X Y)).
  { intermediate_weq (X ╝ Y).
    { apply total2_paths_equiv. }
    use weqbandf.
    { apply hSet_univalence. }
    induction X as [X v], Y as [Y w]; unfold pr1, pr2. intro p.
    induction p.
    change (v = w ≃ @is_WellOrderedSet_map (X,,v) (X,,w) (idfun X))%type.
    induction v as [R i], w as [S j].
    intermediate_weq (R = S).
    { exact (weqonpathsincl _ (@isinclpr1 (hrel_set X) (isWellOrder) (λ R, propproperty _)) (R,,i) (S,,j)). }
    { apply weqiff.
      { split.
        { intros p. intros x y le. induction p. exact le. }
        { intros k. apply funextfun; intros x; apply funextfun; intros y. apply weqlogeq. split.
          { intros r. exact (k _ _ r). }
          { intros s. induction i as [[[[trans refl] anti] tot] min]. apply (squash_to_hProp (tot x y)); intros [c|c].
            { exact c. }
            { induction j as [[[[trans' refl'] anti'] tot'] min'].
              induction (anti' x y s (k y x c)).
              apply refl. } } } }
      { apply propproperty. }
      { apply propproperty. } } }
  intros p. now induction p.
Defined.

Lemma isaprop_weq_WellOrderedSet (X Y : WellOrderedSet) (lem:LEM) : isaprop (X ≅ Y).
Proof.
  apply invproofirrelevance. intros [f i] [g j]. apply subtypeEquality_prop. change (paths f g).
  simple refine (invmap (weqonpathsincl _ (isinclpr1 _ isapropisweq) _ _) _).
  apply funextfun. change (∀ x, f x = g x). apply (proof_by_contradiction lem).
  intros ne; change hfalse. assert (Q := negforall_to_existsneg _ lem ne).
  apply (squash_to_hProp Q); clear Q ne; intros [x' ne].
  set (S := λ x, ¬ (f x = g x) : hProp). assert (Sne := hinhpr(x',,ne) : ∃ x, S x).
  induction (WO_theSmallest Sne) as [x0 [Sx0 x0min]]; change (hProptoType(¬ (f x0 = g x0))) in Sx0.
  apply (squash_to_hProp (WO_istotal Y (f x0) (g x0))); intros [c|c].
  { assert (lt := (c,,Sx0) : (f x0 < g x0)%woset).
    clear c.
    use Sx0; clear Sx0.
    assert (Q := (WellOrderedSet_iso_lt_inv (g,,j) lt) : invmap g (f x0) < invmap g (g x0)); clear lt.
    assert (Q' := Poset_lt_to_nle Q); clear Q.
    induction (!homotinvweqweq g x0).
    assert (K := negf (x0min (invmap g (f x0)) : S (invmap g (f x0)) ⇒ x0 ≤ (invmap g (f x0))) Q'); clear Q'.
    change (dneg (f (invmap g (f x0)) = g (invmap g (f x0)))) in K.
    assert (K' := proof_by_contradiction lem K); clear K.
    assert (e := K' @ homotweqinvweq g (f x0)); clear K'.
    assert (e' := invmaponpathsweq f _ _ e); clear e.
    assert (e := maponpaths g e'); clear e'.
    assert (e' := ! homotweqinvweq g (f x0) @ e); clear e.
    exact e'. }
  { assert (lt : g x0 < f x0).
    { split.
      { exact c. }
      { intros e. use Sx0. exact (!e). } }
    clear c.
    use Sx0; clear Sx0.
    assert (Q := (WellOrderedSet_iso_lt_inv (f,,i) lt) : invmap f (g x0) < invmap f (f x0)); clear lt.
    assert (Q' := Poset_lt_to_nle Q); clear Q.
    induction (!homotinvweqweq f x0).
    assert (K := negf (x0min (invmap f (g x0)) : S (invmap f (g x0)) ⇒ x0 ≤ (invmap f (g x0))) Q'); clear Q'.
    change (dneg (f (invmap f (g x0)) = g (invmap f (g x0)))) in K.
    assert (K' := proof_by_contradiction lem K); clear K.
    assert (K := pathsinv0 K'); clear K'.
    assert (e := K @ homotweqinvweq f (g x0)); clear K.
    assert (e' := invmaponpathsweq g _ _ e); clear e.
    assert (e := maponpaths f e'); clear e'.
    assert (e' := ! homotweqinvweq f (g x0) @ e); clear e.
    exact (!e'). }
Defined.

Lemma isaset_WellOrderedSet (lem:LEM) : isaset WellOrderedSet.
Proof.
  intros X Y.
  exact (isofhlevelweqb 1 (WellOrderedSet_univalence X Y) (isaprop_weq_WellOrderedSet X Y lem)).
Defined.

(** ** An ordered set is well founded iff it is inductively ordered *)

Definition isInductivelyOrdered (X:OrderedSet) : hProp :=
  (
    ∀ (P : X -> hProp) (rec : ∀ x:X, (∀ y, y < x ⇒ P y) ⇒ P x), (∀ x, P x)
  )%oset.

Lemma WellFounded_induction (X:OrderedSet) :
  LEM -> isWellFounded (posetRelation X) -> isInductivelyOrdered X.
Proof.
  intros lem wf P g.
  apply (proof_by_contradiction lem); intro n.
  assert (ne := negforall_to_existsneg _ lem n); clear n.
  induction (@WO_theSmallest (OrderedSet_to_WellOrderedSet X wf) _ ne) as [x0 [nPx0 x0min]];
    change (hProptoType (∀ t : X, ¬ P t ⇒ x0 ≤ t)) in x0min.
  use nPx0; clear nPx0. use g. intros t lt.
  apply (proof_by_contradiction lem); intros nPt;
    change (hProptoType (¬ (P t))) in nPt.
  assert (ge := x0min t nPt); clear nPt.
  exact (gt_to_nle _ _ lt ge).
Defined.

Corollary WellOrderedSet_induction (lem:LEM) (X:WellOrderedSet) : isInductivelyOrdered X.
Proof.
  apply (WellFounded_induction X lem).
  apply WO_isWellFounded.
Defined.

Lemma WellFounded_induction_converse (X:OrderedSet) :
  LEM -> isInductivelyOrdered X -> isWellFounded (posetRelation X).
Proof.
  Open Scope poset.
  Open Scope oset.
  intros lem ind S ne.
  apply (proof_by_contradiction lem); intro n.
  assert (Q := neghexisttoforallneg _ n : ∀ x : X, ¬ (S x ∧ (∀ y : X, S y ⇒ (x ≤ y)%poset))); clear n.
  (** now show that any element of S is bigger that some other element of S *)
  assert (Q' : ∀ x, S x ⇒ ∃ y, S y ∧ y < x).
  { intros x Sx. assert (K := Q x : ¬ (S x ∧ (∀ y : X, S y ⇒ x ≤ y))); clear Q.
    assert (D : ¬ ∀ y : X, S y ⇒ x ≤ y).
    { intros a. use K. exact (Sx,,a). }
    clear K.
    assert (L := negforall_to_existsneg _ lem D); clear D.
    apply (squash_to_hProp L); clear L; intros [t nt].
    assert (M := negimpl_to_conj _ _ lem nt); clear nt.
    induction M as [St nxt].
    apply hinhpr.
    exists t.
    split.
    - exact St.
    - exact (nle_to_gt _ _ nxt). }
  clear Q.
  (** now prove by induction that no element is in S *)
  change hfalse.
  assert (K : ∀ x, ¬ (S x)).
  { apply (ind (λ x, ¬ S x) :
                   (
                     (∀ x:X, (∀ y:X, y < x ⇒ ¬ S y) ⇒ ¬ S x) ⇒ (∀ x, ¬ S x)
                   )).
    intros x hyp.
    intros Sx.
    assert (Q'' := Q' x Sx); clear Q'.
    change hfalse.
    apply (squash_to_hProp Q''); clear Q''; intros [y [Sy lt]].
    exact (hyp y lt Sy). }
  clear Q'.
  apply (squash_to_hProp ne); clear ne; intros [x Sx].
  exact (K x Sx).
Defined.

(** ** Decidable order relations *)

Definition lessthan_choice {X:Poset} (x y:X) : hProp.
Proof.
  intros. apply (coprod_hProp (Poset_lessthan x y) (x = y))%set.
  intros lt. exact (pr2 lt).
Defined.

Notation "m << n" := (lessthan_choice m n) (at level 70, no associativity) :poset.

Lemma lessthan_choice_isrefl {X:Poset} (x:X) : lessthan_choice x x.
Proof.
  exact (ii2 (idpath x)).
Defined.

Lemma lessthan_choice_to_le {X:Poset} (x y:X) : x << y -> x ≤ y.
Proof.
  intros [lt|eq].
  - exact (pr1 lt).
  - induction eq. apply isrefl_posetRelation.
Defined.

Lemma le_to_lessthan_choice {X:Poset} (x y:X) : LEM -> x ≤ y -> x << y.
Proof.
  intros lem le.
  induction (lem (x=y)) as [eq|ne].
  - exact (ii2 eq).
  - exact (ii1 (le,,ne)).
Defined.

Lemma lessthan_choice_trans {X:Poset} (x y z:X) : LEM -> x ≤ y -> y << z -> x << z.
Proof.
  intros lem lxy lyz.
  use le_to_lessthan_choice.
  - exact lem.
  - use (istrans_posetRelation X x y z lxy _). now apply lessthan_choice_to_le.
Defined.

Lemma lessthan_choice_trans' {X:Poset} (x y z:X) :
  LEM -> x << y -> y ≤ z -> x << z.
Proof.
  intros lem lxy lyz.
  use le_to_lessthan_choice.
  - exact lem.
  - use (istrans_posetRelation X x y z _ lyz). now apply lessthan_choice_to_le.
Defined.

Lemma lessthan_choice_trans_2 {X:Poset} (x y z:X) : x << y -> y << z -> x << z.
Proof.
  intros [[lxy nexy]|exy] [[lyz neyz]|eyz].
  - apply ii1. now use (Poset_lt_istrans (y := y)).
  - apply ii1. induction eyz. exact (lxy,,nexy).
  - apply ii1. induction exy. exact (lyz,,neyz).
  - apply ii2. now induction exy, eyz.
Defined.

(** ** Transfinite recursion *)

Local Notation "p ## x" := (transportf _ p x) (right associativity, at level 65). (* for compact displays *)

Section Recursion.

  (**
      To prove that a well ordered set satisfies this well founded recursion principle:

          ∏ (P : X -> hSet) (rec : ∏ x:X, (∏ y, y < x -> P y) -> P x), (∏ x, P x)

      one introduces P and rec and studies partially defined sections of P that are
      "guided" by rec, in the sense that every value is equal to that obtained by applying
      rec to the collection of previous values.

      Then one wants to show that any two guided partial sections take equal values on points
      where both are defined. This can be done with well founded induction, but only because
      the equations are propositions.

      Then one gets a unique largest guided partial section, defined on the union of all of them.
      If its domain is not all of X, one takes the smallest element of X not in the domain
      and adds it to the domain, use rec to extend the definition of the section. achieving a
      contradiction.
   *)

  Section Tools.

    Section A.

      Section A1.

        Context {X:OrderedSet}.

        Definition recursiveHypothesis (P:X->hSet) : UU
          := (∏ x:X, (∏ y, y < x -> P y) -> P x)%type.

      End A1.

      Context (X:OrderedSet).

      Definition isGuidedSection {P:X->hSet} (rec:recursiveHypothesis P) (f : (∏ (x:X), P x)%set) : hProp
        := ∀ (x:X), f x = rec x (λ y yltx, f y).

      Definition isRecursivelyOrdered_unique : hProp
        := ∀ (P:X->hSet) (rec:recursiveHypothesis P), ∃! (f:∏ x, P x), isGuidedSection rec f.

      Definition isRecursivelyOrdered_guided : UU
        := (∏ (P:X->hSet) (rec:recursiveHypothesis P), ∑ (f:∏ x, P x), isGuidedSection rec f)%type.

      Lemma isRecursivelyOrdered_unique_isaprop :
        isInductivelyOrdered X ->
        (∏ (P:X->hSet) (rec:recursiveHypothesis P), isaprop (∑ f, isGuidedSection rec f))%type.
      Proof.
        intros ind P rec. apply invproofirrelevance; intros [f p] [g q].
        (** Show now that any two sections of P guided by [rec] are equal. *)
        assert (e : f = g).
        { apply funextsec. change (∏ x, f x = g x)%set. use ind. intros x H. simple refine (p x @ _ @ ! q x).
          apply maponpaths. apply funextsec; intros y; apply funextsec; intros lt. now use H. }
        induction e. apply maponpaths. apply funextsec; intros x. apply setproperty.
      Defined.

      Definition isRecursivelyOrdered
        := ∏ (P:X->hSet) (rec:recursiveHypothesis P), ∏ x, P x.

      Definition isRecursivelyOrdered_section : isRecursivelyOrdered_unique -> isRecursivelyOrdered
        := λ F P rec, pr11 (F P rec).

      Lemma isRecursivelyOrdered_guided_to_unique :
        isInductivelyOrdered X -> isRecursivelyOrdered_guided -> isRecursivelyOrdered_unique.
      Proof.
        intros ind recgui P rec. apply iscontraprop1.
        - exact (isRecursivelyOrdered_unique_isaprop ind P rec).
        - exact (recgui P rec).
      Defined.

    End A.

    Section B.

      Context {X:OrderedSet} {P:X->hSet} (rec:recursiveHypothesis P).

      Open Scope set.

      Definition isGuidedPartialSection
                 (C:subtype_set X)
                 (f : (∏ (c:X) (Cc : C c), P c)%set)
                 (ini : hProp_to_hSet (isInitial C)) : hProp
        := ∀ (x:X) (Cx:C x),
          f x Cx = rec x (λ y lt, f y (ini y x Cx (Poset_lt_to_le _ _ lt))).

      Definition GuidedPartialSection : hSet
        := ∑ C f ini, isGuidedPartialSection C f ini.

    End B.

    Context {X:OrderedSet} {P:X->hSet} {rec:recursiveHypothesis P}
            (C:GuidedPartialSection rec).

    Definition to_subset  := pr1 C.
    Definition to_section := pr12 C.
    Definition to_initial := pr122 C.
    Definition to_guided  := pr222 C.

  End Tools.

  Context (lem:LEM).

  Theorem OrderedSet_recursion_guided (X:OrderedSet) :
    isInductivelyOrdered X -> isRecursivelyOrdered_guided X.
  Proof.
    intros ind P rec.
    set (isGuidedPartialSection := (λ (C:subtype_set X)
                        (f : (∏ (c:X) (Cc : C c), P c))
                        (ini : hProp_to_hSet (OrderedSet_isInitial C)),
                      ∀ (x:X) (Cx:C x),
                        f x Cx =
                        rec x (λ y lt, f y (ini y x Cx (Poset_lt_to_le _ _ lt))))%set).
    set (G := (∑ C f ini, isGuidedPartialSection C f ini)%type).
    assert (K : (∀ (C D:G) (x:X) (Cx : pr1 C x) (Dx : pr1 D x), pr12 C x Cx = pr12 D x Dx)%set).
    { intros [C [f [ini gui]]] [C' [f' [ini' gui']]]. use ind. intros x hyp Cx C'x.
      simpl in hyp, Cx, C'x.
      simpl.
      simple refine (gui x Cx @ _ @ ! gui' x C'x).
      apply maponpaths.
      apply funextsec; intros y.
      apply funextsec; intros lt.
      apply hyp.
      exact lt. }
    (** Consider the family S of subsets of X that are domains of partial guided sections. *)
    set (S := to_subset : G -> subtype_set X).
    (** For each x, consider those partial sections defined at x. *)
    set (US := subtype_disjoint_union S).
    (** For each one defined at x, provide the value at x. *)
    set (defVal := (λ x C_Cx, to_section (pr1 C_Cx) x (pr2 C_Cx)) : ∏ x (C_Cx : US x), P x).
    (** Form the union C' of their domains. *)
    set (C' := subtype_union S).
    (** Define a partial section f' on C'. *)
    transparent assert (f' : (∏ (x : X) (C'x : C' x), P x)%type).
    { intros x e. use (squash_to_hSet (defVal x) _ e). intros C D. now use K. }
    transparent assert ( ini' : (isInitial C') ).
    { intros x y C'y le. apply (squash_to_hProp C'y); clear C'y; intros C.
      apply hinhpr. exact (pr1 C,,to_initial (pr1 C) x y (pr2 C) le). }
    fold US in ini'.
    assert (C'guided : (isGuidedPartialSection C' f' ini')).
    { intros x C'x.
      apply (squash_to_hProp C'x); intros [C Cx]; change (hProptoType(to_subset C x)) in Cx.
      induction (ishinh_irrel (C,,Cx) C'x). exact (to_guided C x Cx). }
    (** Now we prove everything is in C'. *)
    assert (C'total : ∀ x, C' x).
    { (** We prove it by induction. *)
      use ind. intros x0 hyp.
      (** This is the inductive step, where we prove x0 is in C', using the inductive
          hypothesis [hyp], which says that all smaller elements are in C'. *)
      set (C'' := (λ x:X, x << x0)).
      (** Now we add enough structure to show C'' qualifies for membership
          in [G], so it is contained in C', leading
          to a contradiction. First we define a section f'' on C''. *)
      transparent assert (f'' : (∏ x : X, C'' x -> P x)%type).
      { intros x le. induction le as [lt|eq].
        - use (f' x). now use hyp.
        - simple refine (rec x _). intros y lt. use (f' y).
          use hyp. exact (transportf (λ t, y<t) eq lt). }
      (** Show f' and f'' agree where they are both defined. *)
      assert (f'_f'' : ∀ y e' e'', y < x0 ⇒ f' y e' = f'' y e'').
      { intros y e' [ylt|yeq] lt.
        - change (f'' _ _) with (f' _ (hyp _ ylt)). apply maponpaths; apply propproperty.
        - apply fromempty. induction yeq. exact (Poset_nlt_self lt). }
      assert (f''_x0 : ∏ C''x0, f'' x0 C''x0 = rec x0 (λ y lt, f' y (hyp y lt))).
      { induction C''x0 as [lt|eq].
        - apply fromempty. exact (Poset_nlt_self lt).
        - now induction (uip (setproperty _) (idpath x0) eq). }
      assert (ini'' : isInitial C'').
      { intros x y C''y le. exact (lessthan_choice_trans x y x0 lem le C''y). }
      assert (C''guided : isGuidedPartialSection C'' f'' ini'').
      { intros x [xlt|xeq].
        - change (f'' x _) with (f' x (hyp x xlt)). simple refine (C'guided x _ @ _).
          apply maponpaths; apply funextsec; intro y; apply funextsec; intro lt.
          use f'_f''. now use (Poset_lt_istrans (y := x)).
        - induction xeq. simple refine (f''_x0 (ii2 (idpath x)) @ _).
          apply (maponpaths (rec x)); apply funextsec; intro y; apply funextsec; intro lt.
          now use f'_f''. }
      clear f'_f'' f''_x0.
      set (C''inG := C'',,f'',,ini'',,C''guided : G).
      exact (subtype_union_containedIn S C''inG x0 (lessthan_choice_isrefl x0)). }
    (** We have shown the domain of f' is all of X, so now f' yields the desired section of P. *)
    exists (λ x, f' x (C'total x)).
    (** Now show the section is guided by [rec]. *)
    intros x. simple refine (C'guided x (C'total x) @ _).
    apply maponpaths. apply funextsec; intros y; apply funextsec; intros lt.
    apply maponpaths. apply proofirrelevance_hProp.
  Defined.

  Context (X:WellOrderedSet).

  (** We prefer to use well founded induction, rather than the well founded condition on
      the ordering, because the proof is simpler. *)

  Let ind := WellOrderedSet_induction lem X.

  (** *** The well founded recursion theorem for well ordered sets.  *)

  Open Scope set.

  Open Scope woset.

  Open Scope subtype.

  Theorem WellOrderedSet_recursion_guided : isRecursivelyOrdered_guided X.
  Proof.
    (** One might try also to prove this theorem by following the proof
        of Theorem 3.11 in:
                Well-ordering and choice in toposes
                Mawanda Mbila-Mambu
                Journal of Pure and Applied Algebra
                Volume 50, Issue 2, February 1988, Pages 171-184
                http://www.sciencedirect.com/science/article/pii/0022404988901132 *)
    exact (OrderedSet_recursion_guided X ind).
  Defined.

  Corollary WellOrderedSet_recursion_unique : isRecursivelyOrdered_unique X.
  Proof.
    exact (isRecursivelyOrdered_guided_to_unique X ind WellOrderedSet_recursion_guided).
  Defined.

  Corollary WellOrderedSet_recursion : isRecursivelyOrdered X.
  Proof.
    intros P rec. exact (pr11 (WellOrderedSet_recursion_unique P rec)).
  Defined.

End Recursion.

Lemma bigSet (X:Type) : LEM -> ∑ Y:hSet, ∏ f : Y -> X, ¬ isincl f.
Proof.
  (**
     This lemma is useful in arguments by contradiction, where one uses
     transfinite recursion to define an injective function f, after first
     equipping Y with a well ordering.

     To prove it, let Y be the set of subtypes of X.  It's Cantor's diagonal
     argument that the power set of a set is bigger than the set.
   *)
  intros lem.
  set (PX := subtype_set X). exists PX. intros f inc.
  set (S := (λ x, ∃ T, ∥ x = f T ∥ ∧ ¬ T x)%type).
  set (y := f S).
  apply (logeq_contra (lem (S y))).
  split.
  - intros Sy. apply (squash_to_hProp Sy); intros [T [e' nTy]].
    apply (squash_to_hProp e'); clear e'; intros e.
    assert (E : S = T).
    { apply (isweqonpathsincl f inc _ _ e). }
    induction E, e.
    apply fromempty. exact (nTy Sy).
  - intros nSy. apply hinhpr. exists S. split.
    + apply hinhpr. reflexivity.
    + exact nSy.
Defined.

Corollary bigWellOrderedSet (X:Type) : AxiomOfChoice ⇒ ∃ Y:WellOrderedSet, ∏ f : Y -> X, ¬ isincl f.
Proof.
  intros ac.
  induction (bigSet X (AC_to_LEM ac)) as [V n].
  apply (squash_to_hProp (ZermeloWellOrdering V ac)); intros [R wo].
  apply hinhpr.
  exists (V,,R,,wo).
  exact n.
Defined.

Section Recursion'.

  (** In this section we try to establish recursion over well ordered sets into types of h-level 3, without success. *)

  Open Scope type.

  Section Tools.

    Section A.

      Section A1.

        Context (n:nat) {X:OrderedSet}.

        Definition recursiveHypothesis' (P:X->HLevel n) : UU
          := (∏ x:X, (∏ y, y < x -> P y) -> P x)%type.

      End A1.

      Context (n:nat) (X:OrderedSet).

      Definition isRecursivelyOrdered'
        := (∏ (P:X->HLevel n), recursiveHypothesis' n P -> ∏ x, P x)%type.

    End A.

    Section B.

      Context {X:OrderedSet} {n:nat} {P:X->HLevel n} (rec:recursiveHypothesis' n P).

      Definition isGuidedPartialSection'
                 (C:subtype_set X)
                 (f : (∏ (c:X) (Cc : C c), P c))
                 (ini : hProp_to_hSet (isInitial C)) : UU
        := ∏ (x:X) (Cx:C x),
          f x Cx = rec x (λ y lt, f y (ini y x Cx (Poset_lt_to_le _ _ lt))).

      Definition GuidedPartialSection' : UU
        := ∑ C f ini, isGuidedPartialSection' C f ini.

    End B.

    Context {X:OrderedSet} {n:nat} {P:X->HLevel n} {rec:recursiveHypothesis' n P}
            (C:GuidedPartialSection' rec).

    Definition to_subset'  := pr1 C.
    Definition to_section' := pr12 C.
    Definition to_initial' := pr122 C.
    Definition to_guided'  := pr222 C.

  End Tools.

  Let n := 2 : nat.

  Context (X:OrderedSet) (lem:LEM) (ind : isRecursivelyOrdered' n X).

  Open Scope set.

  Open Scope woset.

  Open Scope subtype.

  Theorem WellOrderedSet_recursion' : isRecursivelyOrdered' (S n) X.
  Proof.
    (** We follow the same general strategy as in [WellOrderedSet_recursion] above. *)
    intros P rec.
    set (G := GuidedPartialSection' rec).
    assert (K : ∏ (x : X) (C : G) (Cx : pr1 C x) (D : G) (Dx : pr1 D x),
                  (to_section' C x Cx = to_section' D x Dx)).
    { use (ind (λ x, HLevelPair n _ _)).
      { repeat (apply impred; intro); exact (pr2 (P x) _ _). }
      intros x hyp C Cx D Dx.
      simple refine (to_guided' _ _ Cx @ _ @ ! to_guided' _ _ Dx).
      apply maponpaths, funextsec; intros y; apply funextsec; intros lt.
      now use hyp. }
    set (SS := to_subset' : G -> subtype_set X).
    set (USS := subtype_disjoint_union SS).
    set (defVal := (λ x C_Cx, to_section' (pr1 C_Cx) x (pr2 C_Cx)) : ∏ x (C_Cx : USS x), P x).
    set (c := λ (x:X) (u u':USS x), K x (pr1 u) (pr2 u) (pr1 u') (pr2 u') : defVal x u = defVal x u').
    set (C' := subtype_union SS).
    transparent assert (f' : (∏ (x : X) (C'x : C' x), P x)%type).
    { intros x e. use (squash_to_HLevel_3 (defVal x) _ _ e).
      - change (const (defVal x)). intros C D. exact (c x C D).
      - intros B C D. change (c x B D = c x B C @ c x C D).
        (** perhaps someone else can figure this out from this point *)
  Abort.

End Recursion'.

Definition isChain {X : Poset} (C : subtype_set X) : hProp := ∀ x y, C x ⇒ (C y ⇒ x ≤ y ∨ y ≤ x).

Definition Chain (X:Poset) : hSet := ∑ C, @isChain X C.

Section PartialFunctions.

  Definition PartialElement (X:hSet) := (∑ P:hPropset, ∏ p:pr1 P, X)%set.
  Definition noElement X : PartialElement X := hfalse,,@fromempty (pr1 X).
  Definition anElement {X:hSet} (x:X) : PartialElement X := htrue,,λ _, x.
  Definition isElement {X:hSet} (x:PartialElement X) : hProp := pr1 x.
  Definition theElement {X:hSet} (x:PartialElement X) : isElement x -> X := pr2 x.
  Definition combinePartialElement {X:hSet} : PartialElement (PartialElement X) -> PartialElement X.
  Proof.
    intros Pf. exists (∑ p, isElement (pr2 Pf p))%prop.
    intros pq. exact (theElement (pr2 Pf (pr1 pq)) (pr2 pq)).
  Defined.
  Definition PartialFunction (T:UU) (X:hSet) := T -> PartialElement X.
  Definition PartialFunction' (T:UU) (X:hSet) := (∑ (P:T->hProp), ∏ t, P t -> X)%type.
  Definition convertPartialFunction' (T:UU) (X:hSet) : PartialFunction' T X -> PartialFunction T X
    := λ f t,pr1 f t,,pr2 f t.
  Definition convertPartialFunction (T:UU) (X:hSet) : PartialFunction T X -> PartialFunction' T X.
  Proof.
    intros f. exists (λ t, pr1 (f t)). exact (λ t, pr2 (f t)).
  Defined.
  Definition isFunction {T:UU} {X:hSet} (f : PartialFunction T X) := ∀ t, isElement (f t).
  Definition toFunction {T:UU} {X:hSet} (f : PartialFunction T X) : isFunction f -> (T -> X)
    := λ a t, theElement (f t) (a t).
  Definition imagePartialFunction {T:UU} {X:hSet} (f : PartialFunction T X) : hsubtype X
    := λ x, ∃ t (i:isElement (f t)), theElement _ i = x.
  Definition isPartialPosetMap {T X:Poset} (f : PartialFunction T X) : hProp
    := ∀ t t' (i:isElement (f t)) (i':isElement (f t')), t ≤ t' ⇒ theElement _ i ≤ theElement _ i'.
  Lemma isChainImagePartial {T:OrderedSet} {X:Poset} (f : PartialFunction T X) :
    isPartialPosetMap f -> isChain (imagePartialFunction f).
  Proof.
    intros ord x y Cx Cy.
    apply (squash_to_hProp Cx); clear Cx; intros [t [i eq]].
    apply (squash_to_hProp Cy); clear Cy; intros [t' [i' eq']].
    induction eq, eq'.
    apply (squash_to_hProp (OrderedSet_istotal t t')).
    intros [c|c'].
    - exact (hinhpr (ii1 (ord t t' i i' c))).
    - exact (hinhpr (ii2 (ord t' t i' i c'))).
  Defined.
  Definition chainImagePartial {T:OrderedSet} {X:Poset} (f : PartialFunction T X) : isPartialPosetMap f -> Chain X
    := λ par, imagePartialFunction f,,isChainImagePartial f par.

End PartialFunctions.

Section Zorn.

  Context (X : Poset).

  Lemma imageIsChainUpto {T : OrderedSet} (f : posetmorphism T X) (t':T) :
    isChain (λ x, ∃ t, t < t' × f t = x).
  Proof.
    intros x y Cx Cy.
    apply (squash_to_hProp Cx); clear Cx; intros [t [p p']].
    apply (squash_to_hProp Cy); clear Cy; intros [u [q q']].
    apply (squash_to_hProp (OrderedSet_istotal t u)); intros [c|c].
    - apply hinhpr, ii1. assert (Q := pr2 f _ _ c). induction p', q'. exact Q.
    - apply hinhpr, ii2. assert (Q := pr2 f _ _ c). induction p', q'. exact Q.
  Defined.

  Definition imageChainUpto {T : OrderedSet} (f : posetmorphism T X) (u:T) : Chain X
    := (λ x, ∃ t, t < u × f t = x) ,, imageIsChainUpto f u.

  Lemma imageChainUpto_eqn {T : OrderedSet} (f g : posetmorphism T X) (u:T) :
    ( ∀ t, t < u ⇒ f t = g t ) -> imageChainUpto f u = imageChainUpto g u.
  Proof.
    intros e. apply subtypeEquality_prop.
    apply funextfun; intros x.
    change ((∃ t, t < u × f t = x) = (∃ t, t < u × g t = x)).
    apply hPropUnivalence.
    - apply hinhfun; intros [t [lt eq]]. exact (t ,, lt ,, ! e t lt @ eq).
    - apply hinhfun; intros [t [lt eq]]. exact (t ,, lt ,,   e t lt @ eq).
  Defined.

  Definition hasUpperBound (C : subtype_set X) := ∃ x, ∀ y (Cy : C y), y ≤ x.

  Definition hasStrictUpperBound (C : subtype_set X) := ∃ x, ∀ y (Cy : C y), y < x.

  Context (bounds : ∀ C : Chain X, hasUpperBound (pr1 C)).

  Lemma Zorn : AxiomOfChoice ⇒ ∃ x:X, isMaximal x.
  Proof.
    intros ac.
    assert (lem := AC_to_LEM ac).
    assert (W := bigWellOrderedSet X ac). apply (squash_to_hProp W); clear W; intros [W noincl].
    apply (proof_by_contradiction lem); intro nomax; change hfalse.
    assert (allnotmax := neghexisttoforallneg _ nomax); clear nomax.
    change (hProptoType (∀ x:X, ¬ isMaximal x)) in allnotmax.
    unfold isMaximal in allnotmax.
    assert (allbigger := (λ x, notMaximal_to_isSmaller _ lem (allnotmax x)) : ∀ x:X, ∃ y, x < y);
      clear allnotmax.
    assert (bounds' : ∀ C:Chain X, hasStrictUpperBound (pr1 C)).
    { intros C. apply (squash_to_hProp (bounds C)); clear bounds; intros [y ge].
      apply (squash_to_hProp (allbigger y)); clear allbigger; intros [y' gt].
      apply hinhpr. exists y'. intros x Cx. exact (Poset_le_lt_istrans (ge x Cx) gt). }
    clear bounds.
    (** For each chain C, choose a strict upper bound. *)
    apply (squash_to_hProp (ac _ _ bounds')); clear bounds'; intros bounds.
    change (∏ C:Chain X, ∑ y, ∀ x, pr1 C x ⇒ x < y)%type in bounds.
    assert (Q : PartialFunction W X).
    { use (WellOrderedSet_recursion lem W).
      intros w hyp.
      (** decide whether the hypothesis is defined everywhere and is order preserving  *)
      set (hyp' := convertPartialFunction' W (PartialElement X) ((λ y, y<w),,hyp) : W -> PartialElement (PartialElement X)).
      set (hyp'' := combinePartialElement ∘ hyp' : PartialFunction W X).
      exists ((∀ y lt, isElement (hyp y lt)) ∧
              (isPartialPosetMap hyp'')).
      intros [def par]. exact (pr1 (bounds (chainImagePartial hyp'' par))). }
  Abort.

End Zorn.
