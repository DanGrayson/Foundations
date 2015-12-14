Require Import UniMath.Ktheory.Representation.
Require Import UniMath.Ktheory.Precategories.
Set Automatic Introduction.

Open Scope cat.

Notation Precategory := Precategory.
Notation functorPrecategory := functorPrecategory.
Notation homset_property := homset_property.

Section A.

  Variable C' : precategory.

  Variable h : has_homsets C'.

  Let C := (C',,h) : Precategory.

  Definition Coproducts := hasBinarySums C.

  Definition CoproductCocone (a b : C') := @BinarySum C a b.

  Definition CoproductObject {a b : C'} (CC : CoproductCocone a b) : C' :=
    universalObject CC.

  Definition CoproductArrow {a b : C'} (CC : CoproductCocone a b) {c : C'}
             (f : a → c) (g : b → c) :
    CoproductObject CC → c
    := binarySumMap CC f g.

  Definition CoproductIn1 {a b : C'} (CC : CoproductCocone a b): a → CoproductObject CC
    := in_1 CC.

  Definition CoproductIn2 {a b : C'} (CC : CoproductCocone a b) : b → CoproductObject CC
    := in_2 CC.

  Definition CoproductOfArrows {a b : C'} (CCab : CoproductCocone a b) {c d : C'}
             (CCcd : CoproductCocone c d) (f : a → c) (g : b → d) :
    CoproductObject CCab → CoproductObject CCcd :=
    CoproductArrow CCab (CoproductIn1 CCcd ∘ f) (CoproductIn2 CCcd ∘ g).

End A.

Section B.

  Variable C' : precategory.
  Variable D' : precategory.

  Variable hC : has_homsets C'.
  Variable hD : has_homsets D'.

  Let C := (C',,hC) : Precategory.
  Let D := (D',,hD) : Precategory.

  Variable HD: Coproducts D' hD.

  Definition coproduct_functor (F G : functor C' D') :
    functor C' D'
    := let F := F:[C,D] in
       let G := G:[C,D] in
       universalObject (functorBinarySum HD F G).

  Definition Coproducts_functor_precat (F G : [C', D', hD]) :
    CoproductCocone [C', D', hD] (functor_category_has_homsets C' D' hD) F G
    := let F := F:[C,D] in
       let G := G:[C,D] in
       functorBinarySum HD F G.

End B.

(*  *)