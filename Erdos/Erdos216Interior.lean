/-
# Erdős Problem 216 with "empty" meaning "no point in the interior"

`Erdos/Erdos216.lean` states emptiness of a convex polygon as: no other point of the set lies
in the closed convex hull of its vertices.  The usual wording, and the wording of the
statement proposed for google-deepmind/formal-conjectures (pull request 6775), is: no point of
the set lies in the *interior* of the convex hull.

This file shows that for point sets with no three points on a line the interior version
implies the closed version (`HasEmptyKGon.of_interior`), and deduces Horton's theorem in the
interior form (`horton_interior`, `horton_cardSetInterior`).

The key lemma is `mem_interior_convexHull`: in a set with no three collinear points, a point
that lies in the convex hull of finitely many other points of the set lies in its interior.
By Carathéodory's theorem the point is a positive combination of at most three of them; one
point is excluded because the point is not a vertex, two because of collinearity, and for
three the point is strictly inside a triangle.
-/
module

public import Erdos.Erdos216

@[expose] public section

open EuclideanGeometry

namespace Erdos216

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- `P` contains an empty convex `k`-gon, with "empty" in the usual sense: `k` points of `P`
in convex position whose convex hull has no point of `P` in its interior. -/
def HasEmptyKGonInterior (k : ℕ) (P : Set ℝ²) : Prop :=
  ∃ S : Finset ℝ², S.card = k ∧ ↑S ⊆ P ∧ ConvexIndep (S : Set ℝ²) ∧
    ∀ p ∈ P, p ∉ interior (convexHull ℝ (S : Set ℝ²))

/-- The set of `N` such that any `N` points in the plane, no three on a line, contain an
empty convex `k`-gon, with "empty" in the interior sense. -/
def cardSetInterior (k : ℕ) : Set ℕ :=
  {N | ∀ pts : Finset ℝ², pts.card = N → NonTrilinear (pts : Set ℝ²) →
    HasEmptyKGonInterior k (pts : Set ℝ²)}

/-! ### Collinearity and the determinant -/

lemma collinear_of_det_eq_zero {a b c : ℝ²} (hab : a ≠ b) (h : det a b c = 0) :
    Collinear ℝ ({a, b, c} : Set ℝ²) := by
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  refine ⟨b - a, ?_⟩
  -- it suffices to write `c - a` as a multiple of `b - a`
  suffices hc : ∃ r : ℝ, c = r • (b - a) +ᵥ a by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact hc
  simp only [det] at h
  have hne : b 0 - a 0 ≠ 0 ∨ b 1 - a 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hab
    ext i
    fin_cases i
    · simpa using (sub_eq_zero.1 hcon.1).symm
    · simpa using (sub_eq_zero.1 hcon.2).symm
  rcases hne with h0 | h1
  · refine ⟨(c 0 - a 0) / (b 0 - a 0), ?_⟩
    ext i
    fin_cases i
    · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        Fin.zero_eta]
      field_simp
      ring
    · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        Fin.mk_one]
      field_simp
      linarith
  · refine ⟨(c 1 - a 1) / (b 1 - a 1), ?_⟩
    ext i
    fin_cases i
    · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        Fin.zero_eta]
      field_simp
      linarith
    · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        Fin.mk_one]
      field_simp
      ring

lemma continuous_det_right (a b : ℝ²) : Continuous fun m : ℝ² => det a b m := by
  unfold det; fun_prop

lemma continuous_det_mid (a q : ℝ²) : Continuous fun m : ℝ² => det a m q := by
  unfold det; fun_prop

lemma continuous_det_left (b q : ℝ²) : Continuous fun m : ℝ² => det m b q := by
  unfold det; fun_prop

/-- A point strictly inside a triangle is in the interior of its convex hull. -/
lemma mem_interior_triangle {a b q m : ℝ²}
    (h : (0 < det a b m ∧ 0 < det a m q ∧ 0 < det m b q) ∨
      (det a b m < 0 ∧ det a m q < 0 ∧ det m b q < 0)) :
    m ∈ interior (convexHull ℝ ({a, b, q} : Set ℝ²)) := by
  rcases h with h | h
  · have hopen : IsOpen {x : ℝ² | 0 < det a b x ∧ 0 < det a x q ∧ 0 < det x b q} :=
      ((isOpen_lt continuous_const (continuous_det_right a b)).inter
        ((isOpen_lt continuous_const (continuous_det_mid a q)).inter
          (isOpen_lt continuous_const (continuous_det_left b q))))
    have hsub : {x : ℝ² | 0 < det a b x ∧ 0 < det a x q ∧ 0 < det x b q} ⊆
        convexHull ℝ ({a, b, q} : Set ℝ²) :=
      fun x hx => mem_convexHull_triple hx.1 hx.2.1 hx.2.2
    exact interior_maximal hsub hopen h
  · have hopen : IsOpen {x : ℝ² | det a b x < 0 ∧ det a x q < 0 ∧ det x b q < 0} :=
      ((isOpen_lt (continuous_det_right a b) continuous_const).inter
        ((isOpen_lt (continuous_det_mid a q) continuous_const).inter
          (isOpen_lt (continuous_det_left b q) continuous_const)))
    have hsub : {x : ℝ² | det a b x < 0 ∧ det a x q < 0 ∧ det x b q < 0} ⊆
        convexHull ℝ ({a, b, q} : Set ℝ²) :=
      fun x hx => mem_convexHull_triple_neg hx.1 hx.2.1 hx.2.2
    exact interior_maximal hsub hopen h

/-! ### The key lemma -/

/-- In a set with no three collinear points, a point lying in the convex hull of finitely
many *other* points of the set lies in the interior of that convex hull. -/
theorem mem_interior_convexHull {P : Set ℝ²} (hgp : NonTrilinear P) {S : Finset ℝ²}
    (hSP : (S : Set ℝ²) ⊆ P) {p : ℝ²} (hpP : p ∈ P) (hpS : p ∉ S)
    (hp : p ∈ convexHull ℝ (S : Set ℝ²)) :
    p ∈ interior (convexHull ℝ (S : Set ℝ²)) := by
  classical
  obtain ⟨ι, _, z, w, hz, hind, hw, hsum, hcomb⟩ := eq_pos_convex_span_of_mem_convexHull hp
  -- at most three points are needed
  have hcard : Fintype.card ι ≤ 3 := by
    have h1 := hind.card_le_finrank_succ
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ Module.finrank ℝ ℝ² :=
      Submodule.finrank_le _
    rw [finrank_euclideanSpace_fin] at h2
    omega
  -- reindex by `Fin n`
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n := ⟨_, rfl⟩
  let e : Fin n ≃ ι := (Fintype.equivFinOfCardEq hn).symm
  have hinj : Function.Injective (z ∘ e) := hind.injective.comp e.injective
  have hsum' : ∑ j, w (e j) = 1 := by rw [← hsum]; exact Equiv.sum_comp e w
  have hcomb' : ∑ j, w (e j) • z (e j) = p := by
    rw [← hcomb]; exact Equiv.sum_comp e (fun i => w i • z i)
  have hzS : ∀ j, z (e j) ∈ (S : Set ℝ²) := fun j => hz ⟨e j, rfl⟩
  have hwpos : ∀ j, 0 < w (e j) := fun j => hw (e j)
  clear_value e
  rw [hn] at hcard
  interval_cases n
  · -- no points: impossible
    simp at hsum'
  · -- one point: `p` would be a vertex
    rw [Fin.sum_univ_one] at hsum' hcomb'
    rw [hsum', one_smul] at hcomb'
    exact absurd (hcomb' ▸ hzS 0) hpS
  · -- two points: `p` would be collinear with them
    exfalso
    rw [Fin.sum_univ_two] at hsum' hcomb'
    set a := z (e 0) with ha
    set b := z (e 1) with hb
    have hab : a ≠ b := fun h => by
      have := hinj h
      simp at this
    have hpa : a ≠ p := fun h => hpS (h ▸ hzS 0)
    have hpb : b ≠ p := fun h => hpS (h ▸ hzS 1)
    have h0 := congrArg (fun x : ℝ² => x 0) hcomb'
    have h1 := congrArg (fun x : ℝ² => x 1) hcomb'
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1
    have hw0 : w (e 0) = 1 - w (e 1) := by linarith
    have hdet : det a b p = 0 := by
      simp only [det, ← h0, ← h1, hw0]; ring
    exact hgp a (hSP (hzS 0)) b (hSP (hzS 1)) p hpP hab hpb hpa
      (collinear_of_det_eq_zero hab hdet)
  · -- three points: `p` is strictly inside their triangle
    rw [Fin.sum_univ_three] at hsum' hcomb'
    set a := z (e 0) with ha
    set b := z (e 1) with hb
    set q := z (e 2) with hq
    have hab : a ≠ b := fun h => by
      have := hinj h
      simp at this
    have hbq : b ≠ q := fun h => by
      have := hinj h
      simp at this
    have haq : a ≠ q := fun h => by
      have := hinj h
      simp at this
    have h0 := congrArg (fun x : ℝ² => x 0) hcomb'
    have h1 := congrArg (fun x : ℝ² => x 1) hcomb'
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1
    have hw0 : w (e 0) = 1 - w (e 1) - w (e 2) := by linarith
    have d1 : det a b p = w (e 2) * det a b q := by
      simp only [det, ← h0, ← h1, hw0]; ring
    have d2 : det a p q = w (e 1) * det a b q := by
      simp only [det, ← h0, ← h1, hw0]; ring
    have d3 : det p b q = w (e 0) * det a b q := by
      simp only [det, ← h0, ← h1]
      rw [hw0]; ring
    have hD : det a b q ≠ 0 := fun h =>
      hgp a (hSP (hzS 0)) b (hSP (hzS 1)) q (hSP (hzS 2)) hab hbq haq
        (collinear_of_det_eq_zero hab h)
    have hsub : ({a, b, q} : Set ℝ²) ⊆ (S : Set ℝ²) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hzS 0
      · exact hzS 1
      · exact hzS 2
    refine interior_mono (convexHull_mono hsub) (mem_interior_triangle ?_)
    rcases lt_or_gt_of_ne hD with hneg | hpos
    · right
      rw [d1, d2, d3]
      exact ⟨mul_neg_of_pos_of_neg (hwpos 2) hneg, mul_neg_of_pos_of_neg (hwpos 1) hneg,
        mul_neg_of_pos_of_neg (hwpos 0) hneg⟩
    · left
      rw [d1, d2, d3]
      exact ⟨mul_pos (hwpos 2) hpos, mul_pos (hwpos 1) hpos, mul_pos (hwpos 0) hpos⟩

/-! ### Consequences -/

/-- For sets with no three collinear points, an empty convex `k`-gon in the interior sense is
an empty convex `k`-gon in the closed sense. -/
theorem HasEmptyKGon.of_interior {k : ℕ} {P : Set ℝ²} (hgp : NonTrilinear P)
    (h : HasEmptyKGonInterior k P) : HasEmptyKGon k P := by
  obtain ⟨S, hcard, hSP, hconv, hempty⟩ := h
  refine ⟨S, hcard, hSP, hconv, ?_⟩
  rintro p ⟨hpP, hpS⟩ hp
  exact hempty p hpP (mem_interior_convexHull hgp hSP hpP (fun h => hpS (Finset.mem_coe.2 h)) hp)

/-- **Horton's theorem, interior form.** For every `k ≥ 7` and every `n` there are `n` points
in the plane, no three on a line, with no convex `k`-gon whose interior is free of points of
the set. -/
theorem horton_interior (k : ℕ) (hk : 7 ≤ k) :
    ∀ n : ℕ, ∃ P : Finset ℝ², P.card = n ∧ NonTrilinear (P : Set ℝ²) ∧
      ¬ HasEmptyKGonInterior k (P : Set ℝ²) := by
  intro n
  obtain ⟨P, hn, hgp, hno⟩ := exists_no_hole_of_seven_le k hk n
  exact ⟨P, hn, hgp, fun h => hno (HasEmptyKGon.of_interior hgp h)⟩

/-- `g(k)` does not exist for `k ≥ 7`, with "empty" in the interior sense. -/
theorem horton_cardSetInterior (k : ℕ) (hk : 7 ≤ k) : cardSetInterior k = ∅ := by
  ext N
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hN
  obtain ⟨P, hc, hgp, hno⟩ := horton_interior k hk N
  exact hno (hN P hc hgp)

end Erdos216

#print axioms Erdos216.horton_cardSetInterior
