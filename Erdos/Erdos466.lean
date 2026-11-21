/-
# Erdős Problem 466

https://www.erdosproblems.com/466

Let `N(X, δ)` be the maximum number of points `P₁, …, Pₙ` in a disc of radius `X`
such that `‖ |Pᵢ - Pⱼ| ‖ ≥ δ` for all `i < j`, where `‖x‖` is the distance from `x` to
the nearest integer.  Is there some `δ > 0` such that `N(X, δ) → ∞` as `X → ∞`?

Yes (Graham).  This file proves the statement, together with Graham's quantitative
bound `N(X, 1/10) > (log X) / 10`.

The definitions `distToNearestInt` and `N`, and the statements of `erdos_466` and
`erdos_466.variants.graham`, are copied verbatim from google-deepmind/formal-conjectures
(`FormalConjectures/ErdosProblems/466.lean`), so that the theorems proved here are
exactly the community statements.

## The proof

Take the points `Pᵢ = (4ⁱ, 2ⁱ)`.  For `j < i` put `a = 4ⁱ - 4ʲ` (a positive integer)
and `b = 2ⁱ - 2ʲ`.  Since `2ⁱ ≥ 2 · 2ʲ`, one checks

  `a / 5 + 1 / 100 ≤ b² ≤ (9 / 5) a + 81 / 100`,

which says exactly that `a + 1/10 ≤ √(a² + b²) ≤ a + 9/10`.  So every distance
`|Pᵢ - Pⱼ|` is at least `1/10` from the nearest integer.  The first `n` points lie
within distance `4ⁿ⁻¹` of `P₀`, giving `N(X, 1/10) ≥ n` once `X ≥ 4ⁿ⁻¹`, i.e.
logarithmically many points.

`N` is defined as a supremum of a set of natural numbers, which is `0` if the set is
unbounded, so we also have to show that a disc holds only boundedly many such points:
the points are pairwise at distance `≥ δ`, and the disc is covered by finitely many
balls of radius `δ / 2`.
-/
import Mathlib

open Filter Metric

namespace Erdos466

/-- The distance from `x` to the nearest integer. (As in formal-conjectures.) -/
noncomputable def distToNearestInt (x : ℝ) : ℝ := |x - round x|

/--
`N X δ` is the maximum number of points in a closed disc of radius `X` in the plane such that
the distance between any two of them is at least `δ` away from the nearest integer.
(As in formal-conjectures.)
-/
noncomputable def N (X δ : ℝ) : ℕ :=
  sSup {n | ∃ (c : EuclideanSpace ℝ (Fin 2)) (P : Finset (EuclideanSpace ℝ (Fin 2))),
    P.card = n ∧ ↑P ⊆ closedBall c X ∧
      (P : Set (EuclideanSpace ℝ (Fin 2))).Pairwise fun x y => δ ≤ distToNearestInt (dist x y)}

/-! ### Generalities about `distToNearestInt` and `N` -/

lemma distToNearestInt_le {x : ℝ} (hx : 0 ≤ x) : distToNearestInt x ≤ x := by
  have h := round_le x 0
  simpa [distToNearestInt, abs_of_nonneg hx] using h

/-- If `x` lies in `[m + δ, m + 1 - δ]` for an integer `m`, it is `δ`-far from every integer. -/
lemma le_distToNearestInt {x δ : ℝ} (m : ℤ) (h₁ : m + δ ≤ x) (h₂ : x ≤ m + 1 - δ) :
    δ ≤ distToNearestInt x := by
  unfold distToNearestInt
  rcases le_or_gt (round x) m with h | h
  · have : ((round x : ℤ) : ℝ) ≤ m := by exact_mod_cast h
    linarith [le_abs_self (x - round x)]
  · have : ((m : ℤ) : ℝ) + 1 ≤ round x := by exact_mod_cast h
    linarith [neg_le_abs (x - round x)]

/-- A disc contains boundedly many points whose mutual distances are `δ`-far from integers. -/
lemma bddAbove_configs (X δ : ℝ) (hδ : 0 < δ) :
    BddAbove {n | ∃ (c : EuclideanSpace ℝ (Fin 2)) (P : Finset (EuclideanSpace ℝ (Fin 2))),
      P.card = n ∧ ↑P ⊆ closedBall c X ∧
        (P : Set (EuclideanSpace ℝ (Fin 2))).Pairwise
          fun x y => δ ≤ distToNearestInt (dist x y)} := by
  obtain ⟨t, -, htfin, hcover⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) X).finite_cover_balls (half_pos hδ)
  refine ⟨htfin.toFinset.card, ?_⟩
  rintro n ⟨c, P, rfl, hP, hpair⟩
  have hex : ∀ p ∈ P, ∃ x ∈ htfin.toFinset, p - c ∈ ball x (δ / 2) := by
    intro p hp
    have hpc : p - c ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) X := by
      have := hP (Finset.mem_coe.2 hp)
      simpa [mem_closedBall, dist_eq_norm] using this
    obtain ⟨x, hx, hpx⟩ := Set.mem_iUnion₂.1 (hcover hpc)
    exact ⟨x, by simpa using hx, hpx⟩
  choose! f hf hfball using hex
  refine Finset.card_le_card_of_injOn f (fun p hp => hf p hp) ?_
  intro p hp q hq hpq
  by_contra hne
  have h1 := hpair hp hq hne
  have h2 : dist p q < δ := by
    have a := mem_ball.1 (hfball p hp)
    have b := mem_ball.1 (hfball q hq)
    rw [hpq] at a
    have h := dist_triangle_right (p - c) (q - c) (f q)
    rw [dist_sub_right] at h
    linarith
  linarith [distToNearestInt_le (dist_nonneg (x := p) (y := q))]

/-- Any admissible configuration of `n` points gives `n ≤ N X δ`. -/
lemma le_N {X δ : ℝ} (hδ : 0 < δ) {n : ℕ} (c : EuclideanSpace ℝ (Fin 2))
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (hcard : P.card = n) (hP : ↑P ⊆ closedBall c X)
    (hpair : (P : Set (EuclideanSpace ℝ (Fin 2))).Pairwise
      fun x y => δ ≤ distToNearestInt (dist x y)) :
    n ≤ N X δ :=
  le_csSup (bddAbove_configs X δ hδ) ⟨c, P, hcard, hP, hpair⟩

/-! ### The construction -/

/-- The point `(4ⁱ, 2ⁱ)`. -/
noncomputable def pt (i : ℕ) : EuclideanSpace ℝ (Fin 2) := !₂[(4 : ℝ) ^ i, (2 : ℝ) ^ i]

lemma dist_pt (i j : ℕ) :
    dist (pt i) (pt j) =
      Real.sqrt (((4 : ℝ) ^ i - 4 ^ j) ^ 2 + ((2 : ℝ) ^ i - 2 ^ j) ^ 2) := by
  simp [pt, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- The key estimate: for `j < i`, the distance `|Pᵢ - Pⱼ|` lies in
`[a + 1/10, a + 9/10]` where `a = 4ⁱ - 4ʲ` is an integer. -/
lemma dist_pt_bounds {i j : ℕ} (hij : j < i) :
    ((4 : ℝ) ^ i - 4 ^ j) + 1 / 10 ≤ dist (pt i) (pt j) ∧
      dist (pt i) (pt j) ≤ ((4 : ℝ) ^ i - 4 ^ j) + 9 / 10 := by
  rw [dist_pt]
  -- write `u = 2ʲ`, `v = 2ⁱ`, so that `v ≥ 2u` and `u ≥ 1`
  have hu : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hv : (2 : ℝ) * 2 ^ j ≤ 2 ^ i := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ (by norm_num) hij
  have h4i : (4 : ℝ) ^ i = (2 ^ i) ^ 2 := by rw [← pow_mul, pow_mul']; norm_num
  have h4j : (4 : ℝ) ^ j = (2 ^ j) ^ 2 := by rw [← pow_mul, pow_mul']; norm_num
  rw [h4i, h4j]
  generalize (2 : ℝ) ^ j = u at hu hv
  generalize (2 : ℝ) ^ i = v at hv
  have ha : 0 ≤ v ^ 2 - u ^ 2 := by nlinarith
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith [mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hv), mul_nonneg (sub_nonneg.2 hu)
      (sub_nonneg.2 hu), mul_nonneg (sub_nonneg.2 hv) (sub_nonneg.2 hv)]
  · apply Real.sqrt_le_iff.2
    refine ⟨by linarith, ?_⟩
    nlinarith [mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hv), mul_nonneg (sub_nonneg.2 hu)
      (sub_nonneg.2 hu), mul_nonneg (sub_nonneg.2 hv) (sub_nonneg.2 hv)]

lemma pt_injective : Function.Injective pt := by
  intro i j h
  have h2 : (2 : ℝ) ^ i = 2 ^ j := by
    have := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) h
    simpa [pt] using this
  exact pow_right_injective₀ (by norm_num) (by norm_num) h2

/-- Distinct points of the construction are at distance `1/10`-far from every integer. -/
lemma pt_far {i j : ℕ} (hij : i ≠ j) :
    (1 / 10 : ℝ) ≤ distToNearestInt (dist (pt i) (pt j)) := by
  wlog h : j < i generalizing i j
  · rw [dist_comm]
    exact this hij.symm (lt_of_le_of_ne (not_lt.1 h) hij)
  obtain ⟨h₁, h₂⟩ := dist_pt_bounds h
  refine le_distToNearestInt ((4 : ℤ) ^ i - 4 ^ j) ?_ ?_
  · push_cast; linarith
  · push_cast; linarith

/-- All points of the construction up to index `i` lie within `4ⁱ` of `P₀`. -/
lemma dist_pt_zero (i : ℕ) : dist (pt i) (pt 0) ≤ (4 : ℝ) ^ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have := (dist_pt_bounds hi).2
    simp only [pow_zero] at this
    linarith

/-- For every `n` the first `n` points of the construction witness `n ≤ N X (1/10)`,
as soon as `4ⁿ⁻¹ ≤ X`. -/
lemma le_N_of_pow_le {X : ℝ} {n : ℕ} (hX : (4 : ℝ) ^ (n - 1) ≤ X) : n ≤ N X (1 / 10) := by
  refine le_N (by norm_num) (pt 0) ((Finset.range n).image pt) ?_ ?_ ?_
  · rw [Finset.card_image_of_injective _ pt_injective, Finset.card_range]
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
    rw [mem_closedBall]
    refine (dist_pt_zero i).trans (le_trans ?_ hX)
    exact pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.1 hi; omega)
  · intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hq)
    exact pt_far (fun h => hpq (h ▸ rfl))

/-! ### The theorems -/

/-- Graham proved that $N(X,1/10)> \frac{\log X}{10}$. -/
theorem erdos_466.variants.graham : ∀ X : ℝ, 1 ≤ X → Real.log X / 10 < N X (1 / 10) := by
  intro X hX
  have hXpos : 0 < X := by linarith
  have hlog : 0 ≤ Real.log X / 10 := div_nonneg (Real.log_nonneg hX) (by norm_num)
  set k := ⌊Real.log X / 10⌋₊ with hk
  have hk1 : Real.log X / 10 < (k + 1 : ℕ) := by
    push_cast; exact Nat.lt_floor_add_one _
  have hk2 : (k : ℝ) ≤ Real.log X / 10 := Nat.floor_le hlog
  have hpow : (4 : ℝ) ^ (k + 1 - 1) ≤ X := by
    rw [Nat.add_sub_cancel]
    calc (4 : ℝ) ^ k ≤ (Real.exp 10) ^ k :=
          pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (10 : ℝ)]) k
      _ = Real.exp (10 * k) := by rw [← Real.exp_nat_mul, mul_comm]
      _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.2 (by linarith)
      _ = X := Real.exp_log hXpos
  have hN : ((k + 1 : ℕ) : ℝ) ≤ N X (1 / 10) := by exact_mod_cast le_N_of_pow_le hpow
  linarith

/--
Let $N(X,\delta)$ denote the maximum number of points $P_1,\ldots,P_n$ which can be chosen in a
circle of radius $X$ such that
$$\| \lvert P_i-P_j\rvert \| \geq \delta$$
for all $1\leq i<j\leq n$. (Here $\|x\|$ is the distance from $x$ to the nearest integer.)

Is there some $\delta>0$ such that
$$\lim_{X\to \infty}N(X,\delta)=\infty?$$

Yes: `δ = 1/10` works.
-/
theorem erdos_466 : ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun X ↦ N X δ) atTop atTop := by
  refine ⟨1 / 10, by norm_num, ?_⟩
  have hreal : Tendsto (fun X : ℝ ↦ (N X (1 / 10) : ℝ)) atTop atTop := by
    have hlog : Tendsto (fun X : ℝ ↦ Real.log X / 10) atTop atTop :=
      Real.tendsto_log_atTop.atTop_div_const (by norm_num)
    refine tendsto_atTop_mono' atTop ?_ hlog
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    exact (erdos_466.variants.graham X hX).le
  exact tendsto_natCast_atTop_iff.1 hreal

end Erdos466

#print axioms Erdos466.erdos_466
#print axioms Erdos466.erdos_466.variants.graham
