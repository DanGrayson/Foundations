(** free monoids *)

(*

We use the generalized associativity and commutativity theorems to constructs free monoids and free
commutative monoids on a type X.  The modules UniMath.Ktheory.Monoid and UniMath.Ktheory.AbelianMonoid
do the same, but with an inductive definition for words.

 *)

Require Export UniMath.Foundations.Sets.

Definition funset_present : bool.
Proof.
  (* make sure funset hasn't already been moved upstream *)
  tryif unify funset funset then fail else exact false.
Defined.

Definition funset X (Y:hSet) : hSet
  := hSetpair (X->Y) (impredfun 2 _ _ (setproperty Y)).

(* these functions come from Ktheory.QuotientSet and should be moved upstream *)
Definition iscomprelfun2 {X Y Z} (RX:hrel X) (RY:hrel Y)
           (f:X->Y->Z) : Type
  := (∏ x x', RX x x' -> ∏ y, f x y = f x' y) ×
     (∏ y y', RY y y' -> ∏ x, f x y = f x y').
Definition iscomprelrelfun2 {X Y Z} (RX:hrel X) (RY:hrel Y) (RZ:hrel Z)
           (f:X->Y->Z) : Type
  := (∏ x x' y, RX x x' -> RZ (f x y) (f x' y)) ×
     (∏ x y y', RY y y' -> RZ (f x y) (f x y')).
Lemma setquotuniv_equal { X : UU } ( R : hrel X ) ( Y : hSet )
      ( f f' : X -> Y ) (p : f = f')
      ( is : iscomprelfun R f ) ( is' : iscomprelfun R f' )
: setquotuniv R Y f is = setquotuniv R Y f' is'.
Proof. intros. destruct p. apply funextsec; intro c.
       assert(ip : isaprop (iscomprelfun R f)). {
         apply impred; intro x; apply impred; intro x'.
         apply impred; intro p. apply setproperty. }
       assert( q : is = is' ). { apply ip. }
       destruct q. reflexivity. Qed.
Definition setquotuniv2 {X Y} (RX:hrel X) (RY:hrel Y)
           {Z:hSet} (f:X->Y->Z) (is:iscomprelfun2 RX RY f) :
  setquot RX -> setquot RY -> Z.
Proof. intros x''.
       simple refine (setquotuniv RX (funset (setquot RY) Z) _ _ _).
       { simpl. intro x. apply (setquotuniv RY Z (f x)).
         intros y y' e. unfold iscomprelfun2 in is.
         apply (pr2 is). assumption. }
       { intros x x' e.
         assert( p : f x = f x' ).
         { apply funextsec; intro y. apply (pr1 is). assumption. }
       apply setquotuniv_equal. assumption. } assumption. Defined.
Definition setquotfun2 {X Y Z} {RX:hrel X} {RY:hrel Y} {RZ:eqrel Z}
           (f:X->Y->Z) (is:iscomprelrelfun2 RX RY RZ f) :
  setquot RX -> setquot RY -> setquot RZ.
Proof. set (f' := fun x y => setquotpr RZ (f x y) : setquotinset RZ).
       apply (setquotuniv2 RX RY f'). split.
       { intros ? ? p ?. apply iscompsetquotpr. exact (pr1 is x x' y p). }
       { intros ? ? p ?. apply iscompsetquotpr. exact (pr2 is x y y' p). }
Defined.
Lemma setquotfun2_equal {X Y Z} (RX:eqrel X) (RY:eqrel Y) (RZ:eqrel Z)
           (f:X->Y->Z) (is:iscomprelrelfun2 RX RY RZ f)
           (x:X) (y:Y) :
  setquotfun2 f is (setquotpr RX x) (setquotpr RY y) =
  setquotpr RZ (f x y).
Proof. reflexivity. (* it computes! *) Defined.

(* move this upstream, too *)
Definition induced_binop {X} (R:eqrel X) (f:binop X) : iscomprelrelfun2 R R R f -> binop (setquot R).
Proof.
  exact (setquotfun2 f).
Defined.

Require Export UniMath.Algebra.IteratedBinaryOperations.

Definition pi0 (X : UU) : UU := setquot (pathseqrel X). (* move upstream, replace pi0 *)

Definition π₀ (X:UU) : hSet.
Proof.
  exists (pi0 X). apply isasetsetquot.
Defined.

Definition isaprop_goal' X (ig:isaprop X) : hProppair X ig -> X.
Proof. intro x. exact x. Defined.

Section AbMonoid.
  Context (X:UU).


  Definition freeAbMonoid : abmonoid.
  Proof.
    set (R := pathseqrel (UnorderedSequence X)).
    assert (lift := issurjsetquotpr R).
    use tpair.
    { exists (π₀ (UnorderedSequence X)). use induced_binop.
      { exact concatenateUnorderedSequence. }
      { split.
        { intros ? ? ?. apply hinhfun. now intros <-. }
        { intros ? ? ?. apply hinhfun. now intros <-. } } }
    simpl.
    repeat split.
    - intros x y z.
      use isaprop_goal'.
      { apply isasetsetquot. }
      generalize (lift x). apply hinhuniv. intro x'. induction x' as [x' x'']. induction x''.
      generalize (lift y). apply hinhuniv. intro y'. induction y' as [y' y'']. induction y''.
      generalize (lift z). apply hinhuniv. intro z'. induction z' as [z' z'']. induction z''.
      apply iscompsetquotpr, hinhpr; simpl; clear lift R.
      apply issoc_concatenateUnorderedSequence.
    - exists (setquotpr R nilUnorderedSequence).
      split.
      { intros x.
        use isaprop_goal'.
        { apply isasetsetquot. }
        generalize (lift x). apply hinhuniv. intro x'. induction x' as [x' x'']. induction x''.
        apply iscompsetquotpr, hinhpr; simpl; clear lift R.



  Abort.

End AbMonoid.
