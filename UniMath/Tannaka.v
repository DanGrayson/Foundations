Require Import UniMath.Foundations.All.

Require Import UniMath.MoreFoundations.All.

Coercion HLevelToType n (X:HLevel n) : Type := pr1 X.

Definition cast {T U:Type} : T = U -> T -> U. (* from Ktheory *)
Proof. intros p t. induction p. exact t. Defined.

Lemma transport_functions {X} {Y:X->Type} {Z:∏ x (y:Y x), Type} (* from Ktheory *)
      {f f':∏ x : X, Y x} (p:f = f') (z:∏ x, Z x (f x)) x :
    transportf (λ f, ∏ x, Z x (f x)) p z x =
    transportf (Z x) (toforallpaths _ _ _ p x) (z x).
Proof. intros. induction p. reflexivity. Defined.

Definition transport_type_path {X Y:Type} (p:X = Y) (x:X) : (* from Ktheory *)
  transportf (λ T:Type, T) p x = cast p x.
Proof. intros. induction p. reflexivity. Defined.

Definition cast_maponpaths {X : UU} (P : X → UU) {x x' : X} (e : x = x') (p : P x) :
  cast (maponpaths P e) p = transportf P e p.
Proof.
  induction e. reflexivity.
Defined.

Lemma HL n (X:Type) : HLevel (S n).
Proof. exists (X -> HLevel n). apply impred; intro x. apply hlevel_of_hlevels. Defined.

Section A.
  Notation ap := maponpaths.
  Notation happly := eqtohomot.
  Notation refl := idpath.
  Context (BG : Type) (lev : isofhlevel 3 BG) (pt : BG).
  Definition eq (x y:BG) : hSet := (x=y),,lev x y.
  Notation "x == y" := (eq x y) (at level 70).
  Context (G := pt = pt).
  Context (Gset := BG -> hSet).
  Context (Xuniv : Gset := λ x, pt == x). (* the regular representation; G as a G-set *)
  Context (F : Gset -> hSet := λ R, R pt). (* send a G-set to its underlying set; the fiber functor *)
  Context (G' := F = F).
  Context (p : G' -> G := λ p, cast (ap pr1hSet (happly p Xuniv)) (refl pt)).
  Context (q : G -> G' := λ g, funextsec _ F F (λ R, ap R g)).
  Lemma A : p ∘ q ~ idfun G.
  Proof.
    unfold G', G.
    intros g.
    unfold funcomp, p, q, idfun.
    assert (M := @toforallpaths_funextsec _ _ F F (λ R : Gset, ap R g)).
    change (@eqtohomot) with (@toforallpaths).
    rewrite M; clear M.
    assert (Q' := maponpathscomp Xuniv pr1hSet g).
    fold hSet; unfold F.
    rewrite Q'; clear Q'.
    change (pr1hSet ∘ (λ x : BG, pt == x)) with (λ x : BG, pt = x).
    rewrite (@cast_maponpaths BG (pr1hSet ∘ Xuniv) pt pt).
    apply transportf_id1.
  Defined.

  Lemma B : q ∘ p ~ idfun G'.
  Proof.
    intros g'. refine (_ @ funextsec_toforallpaths g').
    unfold funcomp, q. apply maponpaths.
    apply funextsec; intro X.
    assert (Q := maponpaths (maponpaths X) (@cast_maponpaths _ pr1hSet _ _ (eqtohomot g' Xuniv) (idpath pt))).
    refine (Q @ _); clear Q.
    unfold G' in g'.
    change (@toforallpaths) with (@eqtohomot).



  Abort.

End A.