Require Export UniMath.Foundations.Combinatorics.FiniteSequences.
Require Export UniMath.Foundations.Algebra.Monoids_and_Groups.
Require Export UniMath.Foundations.Basics.UnivalenceAxiom.

(** general associativity for monoids *)

Local Open Scope multmonoid.

(* we define iterated products in the same way now, with left associativity: *)
Definition sequenceProduct {M:monoid} : Sequence M -> M.
Proof.
  intros [n x].
  induction n as [|n sequenceProduct].
  { exact 1. }
  { exact (sequenceProduct (pr2 (drop (S n,,x) (negpathssx0 _))) * x (lastelement _)). }
Defined.

Definition doubleProduct {M:monoid} : Sequence (Sequence M) -> M.
Proof.
  intros [n x].
  induction n as [|n doubleProduct].
  { exact 1. }
  { exact ((doubleProduct (x ∘ dni_lastelement) * sequenceProduct (x (lastelement _)))). }
Defined.

Definition sequenceProductStep {M:monoid} {n} (x:stn (S n) -> M) :
  sequenceProduct (S n,,x) = sequenceProduct (n,,x ∘ dni_lastelement) * x (lastelement _).
Proof. intros. reflexivity. Defined.

Lemma sequenceProduct9 {M:monoid} (x : stn 0 -> M) :
  sequenceProduct (sequencePair x) = unel M.
Proof.
  reflexivity.
Defined.

Lemma sequenceProduct1 {M:monoid} (x : stn 1 -> M) :
  sequenceProduct (sequencePair x) = x (lastelement 0).
Proof.
  change (sequenceProduct (sequencePair x)) with (unel M * x (lastelement 0)).
  apply lunax.
Defined.

Lemma sequenceProduct_homot {M:monoid} {n} (x y : stn n -> M) :
  x ~ y -> sequenceProduct(n,,x) = sequenceProduct(n,,y).
Proof.
  intros h.
  induction n as [|n N].
  - reflexivity.
  - rewrite 2? sequenceProductStep.
    intermediate_path (sequenceProduct (n,, x ∘ dni_lastelement) * y (lastelement n)).
    + apply maponpaths. exact (h _).
    + apply (maponpaths (λ m, m * _)). apply N. apply funhomot. exact h.
Defined.

Local Definition sequenceProduct_append {M:monoid} (x:Sequence M) (m:M) :
  sequenceProduct (append x m) = sequenceProduct x * m.
Proof. induction x as [n x]. unfold append. rewrite sequenceProductStep.
       unfold funcomp, lastelement.
       Local Opaque sequenceProduct. simpl. Transparent sequenceProduct.
       induction (natlehchoice4 n n (natgthsnn n)) as [p|p].
       { contradicts (isirreflnatlth n) p. }
       { change ((n,, natgthsnn n):stn (S n)) with (lastelement n).
         rewrite append_fun_compute_2.
         apply (maponpaths (λ a, a * m)).
         apply (maponpaths (λ x, sequenceProduct (n,,x))).
         apply funextfun; intros [i b]; simpl.
         now rewrite append_fun_compute_1. }
Defined.

Local Definition doubleProductStep {M:monoid} {n} (x:stn (S n) -> Sequence M) :
  doubleProduct (S n,,x) = doubleProduct (n,,x ∘ dni_lastelement) * sequenceProduct (x (lastelement _)).
Proof. intros. reflexivity. Defined.

(* The general associativity theorem. *)

Theorem associativityOfProducts {M:monoid} (x:Sequence (Sequence M)) :
  sequenceProduct (flatten x) = doubleProduct x.
Proof.
  (* this proof comes from the Associativity theorem, Bourbaki, Algebra, § 1.3, Theorem 1, page 4. *)
  induction x as [n x]. induction n as [|n IHn].
  { reflexivity. }
  { rewrite flattenStep, doubleProductStep.
    generalize (x (lastelement _)) as z; generalize (x ∘ dni_lastelement) as y; clear x.
    intros y z; induction z as [m z].
    induction m as [|m IHm].
    { change (sequenceProduct (0,, z)) with (unel M). rewrite runax.
      rewrite concatenate_0. { exact (IHn y). } { reflexivity. } }
    { rewrite sequenceProductStep, concatenateStep.
      generalize (z (lastelement m)) as w; generalize (z ∘ dni _ (lastelement _)) as v; intros.
      rewrite <- assocax. rewrite sequenceProduct_append.
      apply (maponpaths (λ u, u*w)). apply IHm. } }
Defined.

Corollary associativityOfProducts' {M:monoid} {n} (f:stn n -> nat) (x:stn (stnsum f) -> M) :
  sequenceProduct (stnsum f,,x) = doubleProduct (partition f x).
Proof.
  change (Sequence_to_function (stnsum f,, x)) with x.
  refine (_ @ associativityOfProducts (partition f x)).
  assert (L := flatten_partition f x). apply pathsinv0. exact (sequenceProduct_homot _ _ L).
Defined.

(** commutativity *)

Definition maponpaths2 {X Y Z:UU} (f:X->Y->Z) {x x' y y'} : x=x' -> y=y' -> f x y = f x' y'.
  (* move upstream *)
Proof.
  intros r s. induction r. induction s. reflexivity.
Defined.

Ltac change_lhs a := match goal with |- @paths ?T ?x ?y
                                     => change (@paths T x y) with (@paths T a y) end.
Ltac change_rhs a := match goal with |- @paths ?T ?x ?y
                                     => change (@paths T x y) with (@paths T x a) end.

Lemma commutativityOfProducts_helper {M:abmonoid} {n} (x:stn (S n) -> M) (j:stn (S n)) :
  sequenceProduct (S n,,x) = sequenceProduct (n,,x ∘ dni n j) * x j.
Proof.
  induction j as [j jlt].
  assert (jle := natlthsntoleh _ _ jlt).
  Local Notation "s □ x" := (append s x) (at level 64, left associativity).
  Local Open Scope transport.
  set (f := nil □ j □ S O □ n-j : stn 3 -> nat).
  assert (B : stnsum f = S n).
  { unfold stnsum, f; simpl. repeat unfold append_fun; simpl. rewrite natplusassoc.
    rewrite (natpluscomm 1). rewrite <- natplusassoc.
    rewrite natpluscomm. apply (maponpaths S). rewrite natpluscomm. now apply minusplusnmm. }
  set (r := weqfibtototal _ _ (λ k, eqweqmap (maponpaths (λ n, k < n : UU) B) ) :
              stn (stnsum f) ≃ stn (S n)).
  set (x' := x ∘ r).
  intermediate_path (sequenceProduct (stnsum f,, x')).
  { induction B. apply sequenceProduct_homot. intros i. unfold x'.
    unfold funcomp. apply maponpaths.
    apply ( invmaponpathsincl _ ( isinclstntonat _ ) _ _).
    reflexivity. }
  refine (associativityOfProducts' f x' @ _).
  unfold partition.
  rewrite 3? doubleProductStep.
  change (doubleProduct (0,,_)) with (unel M); rewrite lunax.
  unfold funcomp at 1 2.
  set (s0 := dni_lastelement (dni_lastelement (lastelement 0))).
  unfold funcomp at 1.
  set (s1 := dni_lastelement (lastelement 1)).
  set (s2 := lastelement 2).
  unfold partition'. unfold inverse_lexicalEnumeration.
  change (f s0) with j; change (f s1) with (S O); change (f s2) with (n-j).
  set (f' := nil □ j □ n-j : stn 2 -> nat).
  assert (B' : stnsum f' = n).
  { unfold stnsum, f'; simpl. repeat unfold append_fun; simpl.
    rewrite natpluscomm. now apply minusplusnmm. }
  set (r' := weqfibtototal _ _ (λ k, eqweqmap (maponpaths (λ n, k < n : UU) B') ) :
              stn (stnsum f') ≃ stn n).
  set (x'' := x ∘ dni n (j,, jlt) ∘ r').
  intermediate_path (sequenceProduct (stnsum f',, x'') * x (j,, jlt)).
  { assert (L := sequenceProduct1 (λ j0 : stn 1, x' ((weqstnsum1 f) (s1,, j0)))).
    unfold sequencePair in L.
    rewrite L. rewrite assocax. refine (transportf (λ k, _*k=_) (commax _ _ _) _).
    rewrite <- assocax.
    apply maponpaths2.
    { refine (_ @ !associativityOfProducts' f' x'').
      unfold partition. rewrite 2? doubleProductStep.
      change (doubleProduct (0,,_)) with (unel M); rewrite lunax. apply maponpaths2.
      { unfold funcomp. set (s0' := dni_lastelement (lastelement 0)).
        unfold partition'. change (f' s0') with j.
        apply sequenceProduct_homot. intro i. unfold x', x'', funcomp. apply maponpaths.
        apply (invmaponpathsincl _ ( isinclstntonat _ ) _ _).
        change_lhs (stntonat _ i).
        unfold dni. unfold di.
        match goal with |- context [ natlthorgeh ?x ?y ]
                        => induction (natlthorgeh x y) as [c|c] end.
        { reflexivity. }
        { apply fromempty. assert (P : i ≥ j).
          { exact c. }
          clear c. exact (natlthtonegnatgeh _ _ (stnlt i) P). } }
      { unfold partition'. change (f' (lastelement 1)) with (n-j).
        apply sequenceProduct_homot. intro i. unfold x', x'', funcomp. apply maponpaths.
        apply (invmaponpathsincl _ ( isinclstntonat _ ) _ _).
        change_lhs (j+1+i). unfold dni, di.
        match goal with |- context [ natlthorgeh ?x ?y ]
                        => induction (natlthorgeh x y) as [c|c] end.
        { apply fromempty. exact (negnatlthplusnmn j i c). }
        { change_rhs (1 + (j + i)).
          rewrite <- natplusassoc.
          rewrite (natpluscomm j 1).
          reflexivity.
        }
      }
    }
    unfold x'. unfold funcomp. apply maponpaths.
    apply (invmaponpathsincl _ ( isinclstntonat _ ) _ _).
    match goal with |- ?x = _ => change x with (j+0) end.
    simpl.
    apply natplusr0. }
  { apply (maponpaths (λ k, k * _)). induction (!B'). apply sequenceProduct_homot; intros i.
    unfold x''. unfold funcomp. apply maponpaths.
    apply ( invmaponpathsincl _ ( isinclstntonat _ ) _ _).
    reflexivity. }
Qed.

Theorem commutativityOfProducts {M:abmonoid} {n} (x:stn n->M) (f:stn n ≃ stn n) :
  sequenceProduct (n,,x) = sequenceProduct (n,,x∘f).
Proof.
  (* this proof comes from Bourbaki, Algebra, § 1.5, Theorem 2, page 9 *)
  induction n as [|n IH].
  - reflexivity.
  - set (i := lastelement n); set (i' := f i).
    assert (f' : stn_compl i ≃ stn_compl i'). { apply weqoncompl_ne. }
    set (g := weqdnicompl _ i); set (g' := weqdnicompl _ i').
    rewrite (sequenceProductStep (x ∘ f)).
    change ((x ∘ f) (lastelement n)) with (x i').




    (* assert (specialcase : ∀ (y:stn _->M) (g : stn _ ≃ stn _), g (lastelement n) = lastelement n -> *)
    (*     sequenceProduct (S n,, y) = sequenceProduct (S n,, y ∘ g)). *)
    (* { intros ? ? a. rewrite 2? sequenceProductStep. change ((_ ∘ _) _) with (y (g (lastelement n))). *)
    (*   rewrite a. apply (maponpaths (λ m, m * _)). change (_ ∘ _ ∘ _) with (y ∘ (g ∘ dni_lastelement)). *)


    (*   set (h := eqweqmap (maponpaths stn_compl a)). *)
    (*   assert (pr1_h : ∀ i, pr1 (pr1 (h i)) = pr1 (pr1 i)). { intros. induction a. reflexivity. } *)
    (*   set (wc := weqdnicompl n (lastelement n)). *)
    (*   set (g' := (invweq wc ∘ (h ∘ (weqoncompl_ne g (lastelement n) (stnneq _) (stnneq _) ∘ wc))) %weq). *)
    (*   intermediate_path (sequenceProduct (n,, y ∘ dni_lastelement ∘ g')). *)
    (*   { apply IH. } *)
    (*   { change ((_ ∘ _) ∘ _) with (y ∘ (dni_lastelement ∘ g')). *)
    (*     apply maponpaths; apply maponpaths; apply (maponpaths (λ g, _ ∘ g)). *)
    (*     apply funextfun; intros i. *)
    (*     unfold funcomp. apply isinjstntonat. rewrite pr1_dni_lastelement. unfold g'. *)
    (*     rewrite 3? weqcomp_to_funcomp_app. rewrite inv_weqdnicompl_compute_last. rewrite pr1_h. *)
    (*     unfold pr1weq. *)


    (*     unfold weqoncompl_ne. *)
    (*     change (pr1 *)
    (*        (weqpair *)
    (*           (maponcomplweq_ne g (lastelement n) *)
    (*              (stnneq (lastelement n)) (stnneq (pr1 g (lastelement n)))) *)
    (*           (isweqmaponcompl_ne g (lastelement n) *)
    (*              (stnneq (lastelement n)) (stnneq (pr1 g (lastelement n))))) *)
    (*        (pr1 wc i)) *)
    (*     with (maponcomplweq_ne g (lastelement n) *)
    (*                            (stnneq (lastelement n)) (stnneq (pr1 g (lastelement n))) *)
    (*                            (pr1 wc i) *)
    (*          ). *)
    (*     unfold wc. *)
    (*     unfold weqdnicompl. *)

    (*     induction (natlthorgeh j (lastelement n)) as [t|t]. *)

    (*     rewrite weqdnicompl_compute_last. rewrite pr1_dni_lastelement. *)
    (*     reflexivity. *)
    (*     admit. *)
    (*   }} *)
    (* set (j := f (lastelement n)). *)
    (* induction j as [j jlt]. *)
    (* assert (jle := natlthsntoleh _ _ jlt). *)
    (* Local Open Scope nat. *)
    (* set (m := nil □ j □ 1 □ n-j). *)
    (* set (m' := nil □ j □ n-j □ 1). *)
    (* set (sw := (nil □ ●0 □ ●2 □ ●1 : Sequence (stn 3)) % stn). *)
    (* assert (B : stnsum m = S n). *)
    (* { unfold stnsum; simpl. repeat unfold append_fun; simpl. rewrite natplusassoc. rewrite (natpluscomm 1). rewrite <- natplusassoc. *)
    (*   rewrite natpluscomm. apply (maponpaths S). rewrite natpluscomm. now apply minusplusnmm. } *)
    (* assert (B' : stnsum m' = S n). *)
    (* { unfold stnsum; simpl. rewrite natplusassoc. rewrite (natpluscomm _ 1). rewrite <- natplusassoc. apply B. } *)
    (* assert (C : m' ∘ sw ~ m). *)
    (* { intro i. change (pr1 sw) with 3 in i. *)
    (*   induction i as [i b]. inductive_reflexivity i b. } *)
    (* assert (isweqsw : isweq sw). *)
    (* { apply (gradth sw sw); ( intros [i b]; inductive_reflexivity i b). } *)
    (* set (w := weqstnsum1 m). rewrite B in w. change (pr1 m) with 3 in w. *)
    (* set (w' := weqstnsum1 m'). rewrite B' in w'. change (pr1 m') with 3 in w'. *)

(*
    induction (isdeceqstn (S n) (f (lastelement n)) (lastelement n)) as [p|p].
    + now apply specialcase.
    +
*)

Abort.
