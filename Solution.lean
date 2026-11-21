module

public import Erdos.Erdos216Interior

@[expose] public section

/-!
# Erdős Problem 216: proved statements

The five theorems of `Challenge.lean`, with the same names and statements, proved from the
development in `Erdos/Erdos216.lean` and `Erdos/Erdos216Interior.lean`. The definitions `NonTrilinear`, `ConvexIndep`,
`HasEmptyKGon`, `cardSet`, `HasEmptyKGonInterior` and `cardSetInterior` are those of the
development, which are the same as in
`Challenge.lean`.
-/

namespace Erdos216

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

theorem erdos_216 :
    ∀ n : ℕ, ∃ P : Finset ℝ², P.card = n ∧ NonTrilinear (P : Set ℝ²) ∧
      ¬ HasEmptyKGon 7 (P : Set ℝ²) :=
  exists_no_seven_hole

theorem erdos_216_of_seven_le (k : ℕ) (hk : 7 ≤ k) :
    ∀ n : ℕ, ∃ P : Finset ℝ², P.card = n ∧ NonTrilinear (P : Set ℝ²) ∧
      ¬ HasEmptyKGon k (P : Set ℝ²) :=
  exists_no_hole_of_seven_le k hk

theorem cardSet_eq_empty (k : ℕ) (hk : 7 ≤ k) : cardSet k = ∅ :=
  horton_cardSet k hk

theorem not_forall_cardSet_nonempty : ¬ ∀ k : ℕ, (cardSet k).Nonempty :=
  horton_not_forall

theorem cardSetInterior_eq_empty (k : ℕ) (hk : 7 ≤ k) : cardSetInterior k = ∅ :=
  horton_cardSetInterior k hk

end Erdos216
