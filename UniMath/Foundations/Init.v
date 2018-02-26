(** Initial setup unrelated to Univalent Foundations *)

Require Export Coq.Init.Logic.  (* this fixes the advanced forms of the 'rewrite' tactic, but we want to eliminate it eventually *)

Require Export Coq.Init.Notations. (* get the standard Coq reserved notations *)

(** Notations *)

Notation "'∏'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (* type this in emacs in agda-input method with \prod *)

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).
  (* type this in emacs in agda-input method with \lambda *)

Notation "A -> B" := (forall (_ : A), B) : type_scope.

Notation "X <- Y" := (Y -> X) (at level 90, only parsing, left associativity) : type_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.
(* written \to or \r- in Agda input method *)
(* the level comes from sub/coq/theories/Unicode/Utf8_core.v *)

(** Reserved notations *)

Reserved Notation "'∑'  x .. y , P" (at level 200, x binder, y binder, right associativity).
(* type this in emacs in agda-input method with \sum *)

Reserved Notation "'∃!' x .. y , P" (at level 200, x binder, y binder, right associativity).

Reserved Notation "a != b" (at level 70, no associativity).

Reserved Notation "x :: y" (at level 60, right associativity). (* originally in Coq.Init.Datatypes *)

Reserved Notation "x ++ y" (at level 60, right associativity). (* originally in Coq.Init.Datatypes *)

Reserved Notation "g ∘ f"  (at level 50, left associativity).
(* to input: type "\circ" with Agda input method *)

Reserved Notation "p # x" (right associativity, at level 65, only parsing).

Reserved Notation "a ╝ b" (at level 70, no associativity).
(* in agda input mode use \--= and select the 6-th one in the first set,
   or use \chimney *)

Reserved Notation "X ≃ Y" (at level 80, no associativity). (* parsing looser than x=y, which is at 70 *)
(* to input: type "\simeq" or "\~-" or "\eq" with Agda input method *)

Reserved Notation "p #' x" (right associativity, at level 65, only parsing).

Reserved Notation "f ~ g" (at level 70, no associativity).

Reserved Notation "p @ q" (at level 60, right associativity).

(** Logical operations  *)

Reserved Notation "A ⇒ B" (at level 95, right associativity). (* same as parsing of A <-> B *)
(* tighter than parsing of A -> B and X ≃ Y; right associativity for logical implication *)
(* to input: type "\Rightarrow" or "\r=" or "\r" or "\Longrightarrow" or "\=>" with Agda input method *)

Reserved Notation "A ⇔ B" (at level 95, no associativity). (* same as parsing of A <-> B *)
(* to input: type "\Leftrightarrow" or "\Longleftrightarrow" or "\iff" or "\<=>" or "\lr=" or "\lr" with Agda input method *)

Reserved Notation "X ∨ Y" (at level 85, right associativity). (* same as parsing of \/ *)
(* to input: type "\vee" or "\union" or "\or" with Agda input method *)

Reserved Notation "A ∧ B" (at level 80, right associativity). (* same as parsing of /\ *)
(* to input: type "\wedge" or "\intersection" or "\and" with Agda input method *)

Reserved Notation "'¬¬' X" (at level 75, right associativity). (* the same as parsing of ~ *)
(* type this in emacs in agda-input method with \neg twice *)

Reserved Notation "'¬' X" (at level 75, right associativity). (* the same as parsing of ~ *)
(* type this in emacs in agda-input method with \neg *)

Reserved Notation "x != y" (at level 70).

Reserved Notation "x ≤ y" (at level 70, no associativity). (* same as parsing of < *)
(* type this in emacs in agda-input method with \le *)

Reserved Notation "-1" (at level 0).

Reserved Notation "S ≺ T" (at level 70). (* same as parsing of < *)
(* to input: type "\prec" or "\leq" with Agda input method *)

Reserved Notation "S ≼ T" (at level 70, no associativity).
(* to input: type "\preceq" or "\leq" or "\curlypreceq" with Agda input method *)

Reserved Notation "x ≥ y" (at level 70, no associativity).
(* type this in emacs in agda-input method with \ge *)

Reserved Notation "x /+ y" (at level 40, left associativity). (* parsing like / *)

Reserved Notation "x ≠ y" (at level 70, no associativity).
(* type this in emacs in agda-input method with \ne *)

Reserved Notation " s ∈ T " (at level 70, no associativity).
(* to input: type "\in" or "\member" with Agda input method *)

Reserved Notation " s ∉ T " (at level 70, no associativity).
(* to input: type "\notin" or "\inn" or "\member" with Agda input method *)

Reserved Notation " S ⊆ T " (at level 70, no associativity).
(* to input: type "\sub=" or "\subseteqq" or "\subseteq" or "\leq" with Agda input method *)

Reserved Notation " S ⊈ T " (at level 70, no associativity).
(* to input: type "\nsubseteqq" or "\nsubseteq" or "\sub=n" or "\leqn" with Agda input method *)

Reserved Notation " S ⊊ T " (at level 70, no associativity).
(* to input: type "\subsetneqq" or "\subsetneq" or "\leqn" with Agda input method *)

Reserved Notation " S ≡ T " (at level 70).
(* to input: type "\equiv" or "\eq" or "\==" with Agda input method *)

Reserved Notation "S ≣ T" (at level 70).
(* to input: type "\eq" or "\===" with Agda input method *)

Reserved Notation " S ≢ T " (at level 70).
(* to input: type "\nequiv" or "\eqn" or "\==n" with Agda input method *)

Reserved Notation "⋃ S" (at level 100, no associativity).
(* to input: type "\bigcup" or "\Un" or "\union" with Agda input method *)

Reserved Notation "⋂ S" (at level 100, no associativity).
(* to input: type "\bigcap" or "\I" or "\intersection" with Agda input method *)

Reserved Notation "⟦ n ⟧" (at level 50).
(* in agda-mode \[[ n \]] *)

Reserved Notation "● i" (at level 35).
(* to input: type "\cib" or "\ci" with Agda input method *)

Reserved Notation "x =? y" (at level 70, no associativity). (* same as parsing of = *)

Reserved Notation "x ≐ y" (at level 70, no associativity). (* same as parsing of = *)
(* to input: type "\doteq" or "\.=" or "\eq" with Agda input method *)

Reserved Notation "X ≅ Y" (at level 60, no associativity).
(* written \cong in Agda input method *)

Reserved Notation "A × B" (at level 75, right associativity).
(* type this in emacs in agda-input method with \times *)

Reserved Notation "C ⟦ a , b ⟧" (at level 50).
(* ⟦   to input: type "\[[" or "\(" with Agda input method
   ⟧   to input: type "\]]" or "\)" with Agda input method *)

Reserved Notation "f ;; g"  (at level 50, left associativity, only parsing). (* deprecated *)

Reserved Notation "f · g"  (at level 50, format "f  ·  g", left associativity).
(* to input: type "\centerdot" or "\cdot" with Agda input method *)

Reserved Notation "a --> b" (at level 50).

Reserved Notation "! p " (at level 50).

(* conflict:
    Reserved Notation "# F"  (at level 3).
    Reserved Notation "p # x" (right associativity, at level 65, only parsing).
*)

Reserved Notation "p #' x" (right associativity, at level 65, only parsing).

Reserved Notation "C '^op'" (at level 3, format "C ^op").

Reserved Notation "a <-- b" (at level 50).

Reserved Notation "[ C , D ]" .

Reserved Notation "C [ a , b ]"  (at level 50).

Reserved Notation "X ⟶ Y"  (at level 39).
(* to input: type "\-->" with Agda input method *)

Reserved Notation "X ⟹ Y"  (at level 39).
(* same parsing level as ⟶ *)
(* to input: type "\==>" with Agda input method *)

Reserved Notation "F ∙ G" (at level 35).
(* to input: type "\." with Agda input method *)
(* the old notation had the arguments in the opposite order *)

(* conflict:
    Reserved Notation "s □ x" (at level 64, left associativity).
    Reserved Notation "G □ F" (at level 35).
    (* to input: type "\Box" or "\square" or "\sqw" or "\sq" with Agda input method *)
*)

Reserved Notation "F ◾ b"  (at level 40, left associativity).
(* to input: type "\sqb" or "\sq" with Agda input method *)

Reserved Notation "F ▭ f"  (at level 40, left associativity). (* \rew1 *)
(* to input: type "\rew" or "\re" with Agda input method *)

Reserved Notation "X ⇐ c"   (at level 50).
(* to input: type "\Leftarrow" or "\Longleftarrow" or "\l=" or "\l" with Agda input method *)

Reserved Notation "x ⟲ f"  (at level 50, left associativity).
(* to input: type "\l" and select from the menu, row 4, spot 2, with Agda input method *)

Reserved Notation "q ⟳ x"  (at level 50, left associativity).
(* to input: type "\r" and select from the menu, row 4, spot 3, with Agda input method *)

Reserved Notation "p ◽ b"  (at level 40).
(* to input: type "\sqw" or "\sq" with Agda input method *)

Reserved Notation "xe ⟲⟲ p"  (at level 50).
(* to input: type "\l" and select from the menu, row 4, spot 2, with Agda input method *)

Reserved Notation "r \\ x"  (at level 50, left associativity).

Reserved Notation "x // r"  (at level 50, left associativity).

Reserved Notation "X ⨿ Y" (at level 50, left associativity).
(* type this in emacs with C-X 8 RET AMALGAMATION OR COPRODUCT *)

Reserved Notation "x ,, y" (at level 60, right associativity).

(** Tactics *)

(* Apply this tactic to a proof of ([X] and [X -> ∅]), in either order: *)
Ltac contradicts a b := solve [ induction (a b) | induction (b a) ].

(** A few more tactics, thanks go to Jason Gross *)

Ltac simple_rapply p :=
  simple refine p ||
  simple refine (p _) ||
  simple refine (p _ _) ||
  simple refine (p _ _ _) ||
  simple refine (p _ _ _ _) ||
  simple refine (p _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  simple refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

Tactic Notation "use" uconstr(p) := simple_rapply p.

Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" :=
  simple refine (let name := (_ : type) in _).

Ltac exact_op x := (* from Jason Gross: same as "exact", but with unification the opposite way *)
  let T := type of x in
  let G := match goal with |- ?G => constr:(G) end in
  exact (((λ g:G, g) : T -> G) x).
