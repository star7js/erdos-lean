module

public import Mathlib

@[expose] public section

/-!
# Erdős Problem 216: there is no empty convex 7-gon theorem (Horton)

This is the statement to audit. It imports only Mathlib.

Erdős asked (https://www.erdosproblems.com/216): let `g(k)` be the smallest integer, if one
exists, such that every set of `g(k)` points in the plane, no three on a line, contains an
empty convex `k`-gon, that is, `k` of the points in convex position with no other point of
the set in their convex hull. Does `g(k)` exist?

It is known that `g(3) = 3`, `g(4) = 5`, `g(5) = 10` (Harborth) and `g(6) = 30` (Nicolás and
Gerken for existence, Heule and Scheucher for the value). Horton (*Sets with no empty convex
7-gons*, Canad. Math. Bull. 26 (1983), 482-484) showed that `g(k)` does not exist for
`k ≥ 7`: for every `n` there is a set of `n` points, no three on a line, with no empty
convex 7-gon. The theorems below state Horton's result.

Conventions.

* The plane is `EuclideanSpace ℝ (Fin 2)`.
* "No three on a line" is `NonTrilinear`: no three distinct points of the set are collinear.
* "In convex position" is `ConvexIndep`: no point is in the convex hull of the others.
* "Empty" is stated in two ways. `HasEmptyKGon` says that no other point of the set lies in
  the *closed* convex hull of the `k` points. `HasEmptyKGonInterior` is the textbook wording:
  no point of the set lies in the *interior* of the convex hull. For a set with no three
  points on a line the two agree, since a point of the set on the boundary of the polygon
  would be collinear with two of its vertices. Horton's theorem is stated for both.
-/

namespace Erdos216

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- No three points of `A` lie on a line. -/
def NonTrilinear (A : Set ℝ²) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ {x, y, z}

/-- `S` is in convex position: no point of `S` is in the convex hull of the others. -/
def ConvexIndep (S : Set ℝ²) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

/-- `P` contains an empty convex `k`-gon (a "`k`-hole"): `k` points of `P` in convex position
whose convex hull contains no other point of `P`. -/
def HasEmptyKGon (k : ℕ) (P : Set ℝ²) : Prop :=
  ∃ S : Finset ℝ², S.card = k ∧ ↑S ⊆ P ∧ ConvexIndep S ∧
    ∀ p ∈ P \ S, p ∉ convexHull ℝ (S : Set ℝ²)

/-- The set of `N` such that any `N` points in the plane, no three on a line, contain an
empty convex `k`-gon.  `g(k)` exists iff this set is nonempty. -/
def cardSet (k : ℕ) : Set ℕ :=
  {N | ∀ pts : Finset ℝ², pts.card = N → NonTrilinear (pts : Set ℝ²) →
    HasEmptyKGon k (pts : Set ℝ²)}

/-- **Horton's theorem.** For every `n` there are `n` points in the plane, no three on a
line, with no empty convex 7-gon. -/
theorem erdos_216 :
    ∀ n : ℕ, ∃ P : Finset ℝ², P.card = n ∧ NonTrilinear (P : Set ℝ²) ∧
      ¬ HasEmptyKGon 7 (P : Set ℝ²) := by
  sorry

/-- The same for every `k ≥ 7`: for every `n` there are `n` points in the plane, no three on
a line, with no empty convex `k`-gon. -/
theorem erdos_216_of_seven_le (k : ℕ) (hk : 7 ≤ k) :
    ∀ n : ℕ, ∃ P : Finset ℝ², P.card = n ∧ NonTrilinear (P : Set ℝ²) ∧
      ¬ HasEmptyKGon k (P : Set ℝ²) := by
  sorry

/-- `g(k)` does not exist for `k ≥ 7`: no `N` has the property that every `N` points, no
three on a line, contain an empty convex `k`-gon. -/
theorem cardSet_eq_empty (k : ℕ) (hk : 7 ≤ k) : cardSet k = ∅ := by
  sorry

/-- The answer to Erdős's question is no: it is not the case that `g(k)` exists for every
`k`. -/
theorem not_forall_cardSet_nonempty : ¬ ∀ k : ℕ, (cardSet k).Nonempty := by
  sorry

/-- `P` contains an empty convex `k`-gon, with "empty" in the textbook sense: `k` points of
`P` in convex position whose convex hull has no point of `P` in its interior. -/
def HasEmptyKGonInterior (k : ℕ) (P : Set ℝ²) : Prop :=
  ∃ S : Finset ℝ², S.card = k ∧ ↑S ⊆ P ∧ ConvexIndep (S : Set ℝ²) ∧
    ∀ p ∈ P, p ∉ interior (convexHull ℝ (S : Set ℝ²))

/-- The set of `N` such that any `N` points in the plane, no three on a line, contain an
empty convex `k`-gon, with "empty" in the interior sense. -/
def cardSetInterior (k : ℕ) : Set ℕ :=
  {N | ∀ pts : Finset ℝ², pts.card = N → NonTrilinear (pts : Set ℝ²) →
    HasEmptyKGonInterior k (pts : Set ℝ²)}

/-- `g(k)` does not exist for `k ≥ 7`, with "empty" in the interior sense. This is the form of
Horton's theorem stated as `erdos_216.variants.horton` in pull request 6775 of
google-deepmind/formal-conjectures. -/
theorem cardSetInterior_eq_empty (k : ℕ) (hk : 7 ≤ k) : cardSetInterior k = ∅ := by
  sorry

end Erdos216
