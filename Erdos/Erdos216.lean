/-
# Erdős Problem 216

https://www.erdosproblems.com/216

Let `g(k)` be the smallest integer (if any) such that every set of `g(k)` points in the
plane, no three on a line, contains an empty convex `k`-gon.  Does `g(k)` exist?

Horton (1983): no for `k ≥ 7`.  There are arbitrarily large point sets in general
position with no empty convex 7-gon ("Horton sets").

This file proves it: `erdos_216` (the case `k = 7`) and `erdos_216_of_seven_le` (all
`k ≥ 7`).

## Outline

* Points: `pt i = (i, y i)` with `y i = Σ_j bit_j(i) / B^j`, `B = 2n + 3`.
* `HA`: among indices sharing their `j` lowest binary digits, points with `j`-th digit `1`
  lie above every line through two points with `j`-th digit `0`, and vice versa.
* `not_open`: such a class contains no 4-cup (or 4-cap) with nothing above (below) it.
* `mixed`: a 7-hole meeting both halves of a class has four points in one half; they form
  a cup, a point of that half lies above it, and `mem_convexHull_triple` puts that point
  inside the hole.
* `no_hole`: induction over the digit `j`.

The definitions of `ConvexIndep`, `EmptyShapeIn`
and `HasEmptyKGon` follow bsubercaseaux/EmptyHexagonLean and
google-deepmind/formal-conjectures.
-/
import Mathlib

open EuclideanGeometry

namespace Erdos216

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- No three points of `A` lie on a line. -/
def NonTrilinear (A : Set ℝ²) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ {x, y, z}

/-- `S` is in convex position: no point of `S` is in the convex hull of the others. -/
def ConvexIndep (S : Set ℝ²) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

/-- No point of `P` outside `S` lies in the convex hull of `S`. -/
def EmptyShapeIn (S P : Set ℝ²) : Prop :=
  ∀ p ∈ P \ S, p ∉ convexHull ℝ S

/-- `P` contains an empty convex `k`-gon (a "`k`-hole"). -/
def HasEmptyKGon (k : ℕ) (P : Set ℝ²) : Prop :=
  ∃ S : Finset ℝ², S.card = k ∧ ↑S ⊆ P ∧ ConvexIndep S ∧ EmptyShapeIn S P

/-! ### The geometric input -/

/-- The orientation determinant of three points: positive iff `a, b, c` turn left. -/
def det (a b c : ℝ²) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

/-- If `m` is on the positive side of each of the three directed lines `ab`, `bq`, `qa`
(written here as three positive determinants), then `m` lies in the triangle `a b q`. -/
lemma mem_convexHull_triple {a b q m : ℝ²}
    (h₁ : 0 < det a b m) (h₂ : 0 < det a m q) (h₃ : 0 < det m b q) :
    m ∈ convexHull ℝ ({a, b, q} : Set ℝ²) := by
  have hD : det a b q = det m b q + det a m q + det a b m := by
    simp only [det]; ring
  have hDpos : 0 < det a b q := by rw [hD]; positivity
  have key : m = (det m b q / det a b q) • a + (det a m q / det a b q) • b
      + (det a b m / det a b q) • q := by
    ext i
    fin_cases i <;>
      · simp only [det, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one] at hDpos ⊢
        field_simp
        ring
  rw [key]
  have hsub : ({a, b, q} : Set ℝ²) ⊆ convexHull ℝ ({a, b, q} : Set ℝ²) := subset_convexHull ℝ _
  have ha := hsub (show a ∈ ({a, b, q} : Set ℝ²) by simp)
  have hb := hsub (show b ∈ ({a, b, q} : Set ℝ²) by simp)
  have hq := hsub (show q ∈ ({a, b, q} : Set ℝ²) by simp)
  have hsum : det m b q / det a b q + det a m q / det a b q + det a b m / det a b q = 1 := by
    rw [← add_div, ← add_div, ← hD]; exact div_self hDpos.ne'
  have hconv := convex_convexHull ℝ ({a, b, q} : Set ℝ²)
  have w₁ : 0 < det m b q / det a b q := div_pos h₃ hDpos
  have w₂ : 0 < det a m q / det a b q := div_pos h₂ hDpos
  have w₃ : 0 < det a b m / det a b q := div_pos h₁ hDpos
  -- combine three points in two steps
  have h12 : 0 < det m b q / det a b q + det a m q / det a b q := by positivity
  have hab := hconv ha hb (div_pos w₁ h12).le (div_pos w₂ h12).le
    (by rw [← add_div]; exact div_self h12.ne')
  have := hconv hab hq h12.le w₃.le hsum
  convert this using 1
  rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h12.ne', mul_div_cancel₀ _ h12.ne']


lemma det_swap (a b c : ℝ²) : det b a c = - det a b c := by simp only [det]; ring

/-- The same with all three determinants negative. -/
lemma mem_convexHull_triple_neg {a b q m : ℝ²}
    (h₁ : det a b m < 0) (h₂ : det a m q < 0) (h₃ : det m b q < 0) :
    m ∈ convexHull ℝ ({a, b, q} : Set ℝ²) := by
  have e₁ : 0 < det b a m := by rw [det_swap]; linarith
  have e₂ : 0 < det b m q := by rw [det_swap]; linarith
  have e₃ : 0 < det m a q := by rw [det_swap]; linarith
  have := mem_convexHull_triple e₁ e₂ e₃
  rwa [Set.insert_comm] at this

lemma det_eq_zero_of_collinear {a b c : ℝ²} (h : Collinear ℝ ({a, b, c} : Set ℝ²)) :
    det a b c = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (p₀ := a) (by simp)).1 h
  obtain ⟨rb, rfl⟩ := hv b (by simp)
  obtain ⟨rc, rfl⟩ := hv c (by simp)
  simp only [det, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-! ### Binary digits -/

/-- The `j`-th binary digit of `i`. -/
def bit (j i : ℕ) : ℕ := i / 2 ^ j % 2

lemma bit_lt (j i : ℕ) : bit j i < 2 := Nat.mod_lt _ (by norm_num)

lemma mod_succ (j i : ℕ) : i % 2 ^ (j + 1) = i % 2 ^ j + 2 ^ j * bit j i := Nat.mod_pow_succ

lemma mod_of_mod_succ {j a b : ℕ} (h : a % 2 ^ (j + 1) = b % 2 ^ (j + 1)) :
    a % 2 ^ j = b % 2 ^ j := by
  have hd : 2 ^ j ∣ 2 ^ (j + 1) := pow_dvd_pow 2 (Nat.le_succ j)
  rw [← Nat.mod_mod_of_dvd a hd, ← Nat.mod_mod_of_dvd b hd, h]

lemma bit_of_mod_succ {j a b : ℕ} (h : a % 2 ^ (j + 1) = b % 2 ^ (j + 1)) :
    bit j a = bit j b := by
  have h0 := mod_of_mod_succ h
  rw [mod_succ, mod_succ, h0] at h
  exact Nat.eq_of_mul_eq_mul_left (by positivity) (Nat.add_left_cancel h)

lemma mod_succ_eq {j a b : ℕ} (h : a % 2 ^ j = b % 2 ^ j) (hb : bit j a = bit j b) :
    a % 2 ^ (j + 1) = b % 2 ^ (j + 1) := by
  rw [mod_succ, mod_succ, h, hb]

lemma eq_of_mod_eq_of_le {N j a b : ℕ} (hN : N ≤ j) (ha : a < N) (hb : b < N)
    (h : a % 2 ^ j = b % 2 ^ j) : a = b := by
  have hj : N < 2 ^ j := lt_of_le_of_lt hN Nat.lt_two_pow_self
  rwa [Nat.mod_eq_of_lt (ha.trans hj), Nat.mod_eq_of_lt (hb.trans hj)] at h

/-- Between two indices agreeing in their `j + 1` lowest digits there is one agreeing with
them in the `j` lowest digits but with the opposite `j`-th digit. -/
lemma between {j s t : ℕ} (hst : s < t) (h : s % 2 ^ (j + 1) = t % 2 ^ (j + 1)) :
    s < s + 2 ^ j ∧ s + 2 ^ j < t ∧ (s + 2 ^ j) % 2 ^ j = s % 2 ^ j ∧
      bit j (s + 2 ^ j) ≠ bit j s := by
  have hpos : 0 < 2 ^ j := by positivity
  refine ⟨by omega, ?_, by simp, ?_⟩
  · have hd : 2 ^ (j + 1) ∣ t - s := (Nat.modEq_iff_dvd' hst.le).1 h
    have h1 := Nat.le_of_dvd (by omega) hd
    have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
    omega
  · unfold bit
    rw [Nat.add_div_right _ hpos]
    omega

/-! ### The Horton set -/

/-- Heights of the Horton points: `y B i = Σ_j bit_j(i) / B^j`, so the lowest binary
digit of `i` matters most.  `B` will be taken large compared to the number of points. -/
noncomputable def y (B : ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => ((n + 1) % 2 : ℕ) + y B ((n + 1) / 2) / B
decreasing_by omega

lemma y_eq (B : ℝ) (i : ℕ) : y B i = ((i % 2 : ℕ) : ℝ) + y B (i / 2) / B := by
  cases i with
  | zero => simp [y]
  | succ n => rw [y]

lemma y_bounds {B : ℝ} (hB : 2 ≤ B) (i : ℕ) : 0 ≤ y B i ∧ y B i ≤ 2 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [y]
    · obtain ⟨h1, h2⟩ := ih (i / 2) (Nat.div_lt_self hi (by norm_num))
      rw [y_eq]
      have hm : ((i % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : i % 2 ≤ 1)
      have hm0 : (0 : ℝ) ≤ ((i % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hB0 : 0 < B := by linarith
      have h3 : y B (i / 2) / B ≤ 1 := by rw [div_le_one hB0]; linarith
      have h4 : 0 ≤ y B (i / 2) / B := div_nonneg h1 hB0.le
      constructor <;> linarith

/-- The orientation determinant of the Horton points with indices `a, b, c`. -/
noncomputable def D (B : ℝ) (a b c : ℕ) : ℝ :=
  ((b : ℝ) - a) * (y B c - y B a) - (y B b - y B a) * ((c : ℝ) - a)

lemma D_cyc (B : ℝ) (a b c : ℕ) : D B a b c = D B b c a := by unfold D; ring
lemma D_anti (B : ℝ) (a b c : ℕ) : D B a c b = - D B a b c := by unfold D; ring
lemma D_swap (B : ℝ) (a b c : ℕ) : D B b a c = - D B a b c := by unfold D; ring

/-- Halving three indices of the same parity rescales the determinant. -/
lemma D_half {B : ℝ} (hB : B ≠ 0) {a b c : ℕ} (hab : a % 2 = b % 2) (hac : a % 2 = c % 2) :
    D B a b c = 2 / B * D B (a / 2) (b / 2) (c / 2) := by
  have ca : (a : ℝ) = 2 * ((a / 2 : ℕ) : ℝ) + ((a % 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod a 2).symm
  have cb : (b : ℝ) = 2 * ((b / 2 : ℕ) : ℝ) + ((a % 2 : ℕ) : ℝ) := by
    rw [hab]; exact_mod_cast (Nat.div_add_mod b 2).symm
  have cc : (c : ℝ) = 2 * ((c / 2 : ℕ) : ℝ) + ((a % 2 : ℕ) : ℝ) := by
    rw [hac]; exact_mod_cast (Nat.div_add_mod c 2).symm
  have ya := y_eq B a
  have yb := y_eq B b
  have yc := y_eq B c
  rw [← hab] at yb
  rw [← hac] at yc
  simp only [D]
  rw [ya, yb, yc, ca, cb, cc]
  field_simp
  ring

lemma key_pos {e n x z ta tb tc : ℝ} (hx : 1 ≤ x) (hz : |z| ≤ n) (hn : 0 ≤ n)
    (ha0 : 0 ≤ ta) (ha1 : ta ≤ e) (hb0 : 0 ≤ tb) (hb1 : tb ≤ e) (hc0 : 0 ≤ tc)
    (heN : e * (n + 1) < 1) : 0 < x * (1 + tc - ta) - (tb - ta) * z := by
  have he0 : 0 ≤ e := le_trans ha0 ha1
  have h1 : |(tb - ta) * z| ≤ e * n := by
    rw [abs_mul]
    exact mul_le_mul (by rw [abs_le]; constructor <;> linarith) hz (abs_nonneg _) he0
  have h2 := (abs_le.1 h1).2
  have h3 : 0 ≤ (x - 1) * (1 + tc - ta) := by
    apply mul_nonneg (by linarith)
    nlinarith
  nlinarith

lemma key_neg {e n x z ta tb tc : ℝ} (hx : 1 ≤ x) (hz : |z| ≤ n) (hn : 0 ≤ n)
    (ha0 : 0 ≤ ta) (ha1 : ta ≤ e) (hb0 : 0 ≤ tb) (hb1 : tb ≤ e) (hc1 : tc ≤ e)
    (heN : e * (n + 1) < 1) : x * (tc - (1 + ta)) - (1 + tb - (1 + ta)) * z < 0 := by
  have he0 : 0 ≤ e := le_trans ha0 ha1
  have h1 : |(tb - ta) * z| ≤ e * n := by
    rw [abs_mul]
    exact mul_le_mul (by rw [abs_le]; constructor <;> linarith) hz (abs_nonneg _) he0
  have h2 := (abs_le.1 h1).1
  have h3 : 0 ≤ (x - 1) * (1 + ta - tc) := by
    apply mul_nonneg (by linarith)
    nlinarith
  nlinarith

/-- Level `0`: an odd-indexed point lies above every line through two even-indexed points,
and an even-indexed point lies below every line through two odd-indexed points. -/
lemma HA_zero {N : ℕ} {B : ℝ} (hB : (2 : ℝ) * N + 3 ≤ B) {a b c : ℕ} (hab : a < b)
    (hb : b < N) (hc : c < N) (h1 : a % 2 = b % 2) (h2 : c % 2 ≠ a % 2) :
    (a % 2 = 0 → 0 < D B a b c) ∧ (a % 2 = 1 → D B a b c < 0) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hB0 : 0 < B := by linarith
  have hB2 : 2 ≤ B := by linarith
  have heN : 2 / B * ((N : ℝ) + 1) < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hB0]; linarith
  have tb : ∀ i, 0 ≤ y B i / B ∧ y B i / B ≤ 2 / B := fun i =>
    ⟨div_nonneg (y_bounds hB2 i).1 hB0.le, div_le_div_of_nonneg_right (y_bounds hB2 i).2 hB0.le⟩
  have hba : (1 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
    linarith
  have hca : |(c : ℝ) - a| ≤ N := by
    have e1 : (c : ℝ) ≤ N := by exact_mod_cast hc.le
    have e2 : (a : ℝ) ≤ N := by exact_mod_cast (by omega : a ≤ N)
    have e3 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    have e4 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    rw [abs_le]; constructor <;> linarith
  obtain ⟨ta0, ta1⟩ := tb (a / 2)
  obtain ⟨tb0, tb1⟩ := tb (b / 2)
  obtain ⟨tc0, tc1⟩ := tb (c / 2)
  have ya := y_eq B a
  have yb := y_eq B b
  have yc := y_eq B c
  rw [← h1] at yb
  constructor
  · intro h0
    have hc1 : c % 2 = 1 := by omega
    rw [h0] at ya yb
    rw [hc1] at yc
    have k := key_pos hba hca hN ta0 ta1 tb0 tb1 tc0 heN
    simp only [D]
    rw [ya, yb, yc]
    push_cast
    linarith
  · intro h0
    have hc1 : c % 2 = 0 := by omega
    rw [h0] at ya yb
    rw [hc1] at yc
    have k := key_neg hba hca hN ta0 ta1 tb0 tb1 tc1 heN
    simp only [D]
    rw [ya, yb, yc]
    push_cast
    linarith

/-- **High above / deep below.**  Among indices agreeing in their `j` lowest digits, a point
whose `j`-th digit is `1` lies above every line through two points whose `j`-th digit is `0`,
and vice versa. -/
lemma HA {N : ℕ} {B : ℝ} (hB : (2 : ℝ) * N + 3 ≤ B) : ∀ (j a b c : ℕ), a < b → b < N → c < N →
    a % 2 ^ j = b % 2 ^ j → a % 2 ^ j = c % 2 ^ j → bit j a = bit j b → bit j c ≠ bit j a →
    (bit j a = 0 → 0 < D B a b c) ∧ (bit j a = 1 → D B a b c < 0) := by
  intro j
  induction j with
  | zero =>
    intro a b c hab hb hc _ _ h1 h2
    simp only [bit, pow_zero, Nat.div_one] at h1 h2 ⊢
    exact HA_zero hB hab hb hc h1 h2
  | succ j ih =>
    intro a b c hab hb hc h1 h2 h3 h4
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hBpos : 0 < B := by linarith
    have par : ∀ {u v : ℕ}, u % 2 ^ (j + 1) = v % 2 ^ (j + 1) →
        u % 2 = v % 2 ∧ (u / 2) % 2 ^ j = (v / 2) % 2 ^ j := by
      intro u v h
      constructor
      · have hd : 2 ∣ 2 ^ (j + 1) := dvd_pow_self 2 (Nat.succ_ne_zero j)
        rw [← Nat.mod_mod_of_dvd u hd, ← Nat.mod_mod_of_dvd v hd, h]
      · rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, ← pow_succ', h]
    have hbit : ∀ u, bit (j + 1) u = bit j (u / 2) := by
      intro u; unfold bit; rw [pow_succ', Nat.div_div_eq_div_mul]
    obtain ⟨p1, q1⟩ := par h1
    obtain ⟨p2, q2⟩ := par h2
    have hD := D_half hBpos.ne' p1 p2
    have hpos : 0 < 2 / B := by positivity
    rw [hbit a, hbit b] at h3
    rw [hbit c, hbit a] at h4
    obtain ⟨i1, i2⟩ := ih (a / 2) (b / 2) (c / 2) (by omega) (by omega) (by omega) q1 q2 h3 h4
    rw [hbit a, hD]
    exact ⟨fun h => mul_pos hpos (i1 h), fun h => mul_neg_of_pos_of_neg hpos (i2 h)⟩

lemma HA_ne {N : ℕ} {B : ℝ} (hB : (2 : ℝ) * N + 3 ≤ B) {j a b c : ℕ} (hab : a ≠ b)
    (ha : a < N) (hb : b < N) (hc : c < N) (h1 : a % 2 ^ j = b % 2 ^ j)
    (h2 : a % 2 ^ j = c % 2 ^ j) (h3 : bit j a = bit j b) (h4 : bit j c ≠ bit j a) :
    D B a b c ≠ 0 := by
  have key : ∀ a b : ℕ, a < b → b < N → a % 2 ^ j = b % 2 ^ j → a % 2 ^ j = c % 2 ^ j →
      bit j a = bit j b → bit j c ≠ bit j a → D B a b c ≠ 0 := by
    intro a b hab hb h1 h2 h3 h4
    obtain ⟨i1, i2⟩ := HA hB j a b c hab hb hc h1 h2 h3 h4
    have := bit_lt j a
    rcases (by omega : bit j a = 0 ∨ bit j a = 1) with h | h
    · exact (i1 h).ne'
    · exact (i2 h).ne
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h hb h1 h2 h3 h4
  · have := key b a h ha h1.symm (h1.symm.trans h2) h3.symm (by rw [← h3]; exact h4)
    rw [D_swap] at this
    simpa using this

/-- Any three distinct Horton points are non-collinear. -/
theorem D_ne_zero {N : ℕ} {B : ℝ} (hB : (2 : ℝ) * N + 3 ≤ B) : ∀ (k j : ℕ), N ≤ j + k →
    ∀ a b c : ℕ, a < N → b < N → c < N → a ≠ b → b ≠ c → a ≠ c →
    a % 2 ^ j = b % 2 ^ j → a % 2 ^ j = c % 2 ^ j → D B a b c ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro j hN a b c ha hb hc hab _ _ h1 _
    exact absurd (eq_of_mod_eq_of_le (by omega) ha hb h1) hab
  | succ k ih =>
    intro j hN a b c ha hb hc hab hbc hac h1 h2
    have la := bit_lt j a
    have lb := bit_lt j b
    have lc := bit_lt j c
    by_cases e1 : bit j a = bit j b
    · by_cases e2 : bit j a = bit j c
      · exact ih (j + 1) (by omega) a b c ha hb hc hab hbc hac (mod_succ_eq h1 e1)
          (mod_succ_eq h2 e2)
      · exact HA_ne hB hab ha hb hc h1 h2 e1 (fun h => e2 h.symm)
    · by_cases e2 : bit j a = bit j c
      · have := HA_ne hB hac ha hc hb h2 h1 e2 (fun h => e1 h.symm)
        rw [D_anti] at this
        simpa using this
      · have := HA_ne hB hbc hb hc ha (h1.symm.trans h2) h1.symm (by omega) (by omega)
        rwa [← D_cyc] at this

/-! ### The combinatorial core

We argue with an abstract "orientation" `E` and a digit `β` marking which half is the lower
one, so that the same lemmas cover cups (`E = D`, `β = 0`) and caps (`E = -D`, `β = 1`). -/

/-- The properties of the orientation function used by the combinatorial argument. -/
structure Sys (N β : ℕ) (E : ℕ → ℕ → ℕ → ℝ) : Prop where
  hβ : β < 2
  cyc : ∀ a b c, E a b c = E b c a
  anti : ∀ a b c, E a c b = - E a b c
  ha1 : ∀ j a b c, a < b → b < N → c < N → a % 2 ^ j = b % 2 ^ j → a % 2 ^ j = c % 2 ^ j →
    bit j a = β → bit j b = β → bit j c ≠ β → 0 < E a b c
  ha2 : ∀ j a b c, a < b → b < N → c < N → a % 2 ^ j = b % 2 ^ j → a % 2 ^ j = c % 2 ^ j →
    bit j a ≠ β → bit j b ≠ β → bit j c = β → E a b c < 0

/-- **No open 4-cup.**  If `a < b < c < d` agree in their `j` lowest digits and form a cup,
then some point of the same class lies strictly above one of the three segments of the cup. -/
theorem not_open {N β : ℕ} {E : ℕ → ℕ → ℕ → ℝ} (S : Sys N β E) : ∀ (k j : ℕ), N ≤ j + k →
    ∀ (a b c d : ℕ), a < b → b < c → c < d → d < N →
    a % 2 ^ j = b % 2 ^ j → a % 2 ^ j = c % 2 ^ j → a % 2 ^ j = d % 2 ^ j →
    0 ≤ E a b c → 0 ≤ E a b d → 0 ≤ E b c d →
    ∃ p s t, ((s = a ∧ t = b) ∨ (s = b ∧ t = c) ∨ (s = c ∧ t = d)) ∧ s < p ∧ p < t ∧
      p % 2 ^ j = a % 2 ^ j ∧ 0 < E s t p := by
  intro k
  induction k with
  | zero =>
    intro j hN a b c d hab hbc hcd hd h1 _ _ _ _ _
    exact absurd (eq_of_mod_eq_of_le (by omega) (by omega) (by omega) h1) (by omega)
  | succ k ih =>
    intro j hN a b c d hab hbc hcd hd h1 h2 h3 e1 e2 e3
    have adj : ∀ s t, s < t → t < N → s % 2 ^ j = a % 2 ^ j → t % 2 ^ j = a % 2 ^ j →
        bit j s = β → bit j t = β →
        ∃ p, s < p ∧ p < t ∧ p % 2 ^ j = a % 2 ^ j ∧ 0 < E s t p := by
      intro s t hst ht hs ht' bs bt
      obtain ⟨g1, g2, g3, g4⟩ :=
        between hst (mod_succ_eq (hs.trans ht'.symm) (bs.trans bt.symm))
      refine ⟨s + 2 ^ j, g1, g2, g3.trans hs, ?_⟩
      exact S.ha1 j s t (s + 2 ^ j) hst ht (g2.trans ht) (hs.trans ht'.symm) g3.symm bs bt
        (by rw [← bs]; exact g4)
    have lul : ∀ s m t, s < m → m < t → t < N → s % 2 ^ j = m % 2 ^ j →
        s % 2 ^ j = t % 2 ^ j → bit j s = β → bit j t = β → bit j m ≠ β → 0 ≤ E s m t →
        False := by
      intro s m t hsm hmt ht hm ht' bs bt bm he
      have g1 := S.ha1 j s t m (hsm.trans hmt) ht (hmt.trans ht) ht' hm bs bt bm
      have g2 := S.anti s m t
      linarith
    by_cases ba : bit j a = β
    · by_cases bb : bit j b = β
      · obtain ⟨p, hp⟩ := adj a b hab (by omega) rfl h1.symm ba bb
        exact ⟨p, a, b, Or.inl ⟨rfl, rfl⟩, hp⟩
      · by_cases bc : bit j c = β
        · exact (lul a b c hab hbc (by omega) h1 h2 ba bc bb e1).elim
        · by_cases bd : bit j d = β
          · exact (lul a b d hab (hbc.trans hcd) hd h1 h3 ba bd bb e2).elim
          · have g1 := S.ha2 j b c a hbc (by omega) (by omega) (h1.symm.trans h2) h1.symm
              bb bc ba
            have g2 := S.cyc a b c
            linarith
    · by_cases bb : bit j b = β
      · by_cases bc : bit j c = β
        · obtain ⟨p, hp⟩ := adj b c hbc (by omega) h1.symm h2.symm bb bc
          exact ⟨p, b, c, Or.inr (Or.inl ⟨rfl, rfl⟩), hp⟩
        · by_cases bd : bit j d = β
          · exact (lul b c d hbc hcd hd (h1.symm.trans h2) (h1.symm.trans h3) bb bd bc e3).elim
          · have g1 := S.ha2 j c d b hcd hd (by omega) (h2.symm.trans h3) (h2.symm.trans h1)
              bc bd bb
            have g2 := S.cyc b c d
            linarith
      · by_cases bc : bit j c = β
        · by_cases bd : bit j d = β
          · obtain ⟨p, hp⟩ := adj c d hcd hd h2.symm h3.symm bc bd
            exact ⟨p, c, d, Or.inr (Or.inr ⟨rfl, rfl⟩), hp⟩
          · have g1 := S.ha2 j a b c hab (by omega) (by omega) h1 h2 ba bb bc
            linarith
        · by_cases bd : bit j d = β
          · have g1 := S.ha2 j b c d hbc (by omega) hd (h1.symm.trans h2) (h1.symm.trans h3)
              bb bc bd
            linarith
          · have hβ := S.hβ
            have eqb : ∀ {u v : ℕ}, bit j u ≠ β → bit j v ≠ β → bit j u = bit j v := by
              intro u v hu hv
              have := bit_lt j u
              have := bit_lt j v
              omega
            obtain ⟨p, s, t, hst, hsp, hpt, hpm, hE⟩ := ih (j + 1) (by omega) a b c d hab hbc
              hcd hd (mod_succ_eq h1 (eqb ba bb)) (mod_succ_eq h2 (eqb ba bc))
              (mod_succ_eq h3 (eqb ba bd)) e1 e2 e3
            exact ⟨p, s, t, hst, hsp, hpt, mod_of_mod_succ hpm, hE⟩

/-- **A hole cannot straddle both halves.**  Let `X` be a convex-independent set of points
of one class which is empty in that class.  Then `X` cannot contain four points of the
lower half together with a point of the upper half. -/
theorem mixed {N β : ℕ} {E : ℕ → ℕ → ℕ → ℝ} (S : Sys N β E) (P : ℕ → ℝ²)
    (hinj : Function.Injective P)
    (hG : ∀ a b q m, 0 < E a b m → 0 < E a m q → 0 < E m b q →
      P m ∈ convexHull ℝ ({P a, P b, P q} : Set ℝ²))
    (j r : ℕ) (X : Finset ℕ) (hX : ∀ i ∈ X, i < N ∧ i % 2 ^ j = r)
    (hconv : ConvexIndep (P '' (X : Set ℕ)))
    (hempty : ∀ i, i < N → i % 2 ^ j = r → i ∉ X → P i ∉ convexHull ℝ (P '' (X : Set ℕ)))
    (h4 : 4 ≤ (X.filter (fun i => bit j i = β)).card) (q : ℕ) (hq : q ∈ X)
    (hqb : bit j q ≠ β) : False := by
  obtain ⟨qN, qr⟩ := hX q hq
  -- three lower points of `X` never form a cap
  have tri : ∀ s m t, s ∈ X → m ∈ X → t ∈ X → bit j s = β → bit j m = β → bit j t = β →
      s < m → m < t → E s t m ≤ 0 := by
    intro s m t hs hm ht bs bm bt hsm hmt
    by_contra hpos
    push Not at hpos
    obtain ⟨sN, sr⟩ := hX s hs
    obtain ⟨mN, mr⟩ := hX m hm
    obtain ⟨tN, tr⟩ := hX t ht
    have e1 := S.ha1 j s m q hsm mN qN (sr.trans mr.symm) (sr.trans qr.symm) bs bm hqb
    have e2 := S.ha1 j m t q hmt tN qN (mr.trans tr.symm) (mr.trans qr.symm) bm bt hqb
    have hmem := hG s t q m hpos e1 e2
    refine hconv (P m) ⟨m, hm, rfl⟩ (convexHull_mono ?_ hmem)
    have hne : ∀ u, u ∈ X → u ≠ m → P u ∈ P '' (X : Set ℕ) \ {P m} :=
      fun u hu hum => ⟨⟨u, hu, rfl⟩, fun h => hum (hinj h)⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hne s hs (by omega)
    · exact hne t ht (by omega)
    · exact hne q hq (by rintro rfl; exact hqb bm)
  -- four lower points of `X`, in increasing order
  let f := (X.filter (fun i => bit j i = β)).orderEmbOfCardLe h4
  have fX : ∀ i, f i ∈ X ∧ bit j (f i) = β := fun i =>
    Finset.mem_filter.1 (Finset.orderEmbOfCardLe_mem _ h4 i)
  have f01 : f 0 < f 1 := f.strictMono (by decide)
  have f12 : f 1 < f 2 := f.strictMono (by decide)
  have f23 : f 2 < f 3 := f.strictMono (by decide)
  have fr : ∀ i, f i % 2 ^ j = r := fun i => (hX _ (fX i).1).2
  have fN : ∀ i, f i < N := fun i => (hX _ (fX i).1).1
  have c1 : 0 ≤ E (f 0) (f 1) (f 2) := by
    have := tri _ _ _ (fX 0).1 (fX 1).1 (fX 2).1 (fX 0).2 (fX 1).2 (fX 2).2 f01 f12
    have := S.anti (f 0) (f 1) (f 2)
    linarith
  have c2 : 0 ≤ E (f 0) (f 1) (f 3) := by
    have := tri _ _ _ (fX 0).1 (fX 1).1 (fX 3).1 (fX 0).2 (fX 1).2 (fX 3).2 f01 (f12.trans f23)
    have := S.anti (f 0) (f 1) (f 3)
    linarith
  have c3 : 0 ≤ E (f 1) (f 2) (f 3) := by
    have := tri _ _ _ (fX 1).1 (fX 2).1 (fX 3).1 (fX 1).2 (fX 2).2 (fX 3).2 f12 f23
    have := S.anti (f 1) (f 2) (f 3)
    linarith
  have lev : ∀ i, f 0 % 2 ^ (j + 1) = f i % 2 ^ (j + 1) := fun i =>
    mod_succ_eq ((fr 0).trans (fr i).symm) ((fX 0).2.trans (fX i).2.symm)
  obtain ⟨p, s, t, hst, hsp, hpt, hpm, hE⟩ := not_open S N (j + 1) (by omega) (f 0) (f 1) (f 2)
    (f 3) f01 f12 f23 (fN 3) (lev 1) (lev 2) (lev 3) c1 c2 c3
  have hs : (s ∈ X ∧ bit j s = β) ∧ (t ∈ X ∧ bit j t = β) := by
    rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨fX _, fX _⟩
  obtain ⟨⟨sX, bs⟩, ⟨tX, bt⟩⟩ := hs
  obtain ⟨sN, sr⟩ := hX s sX
  obtain ⟨tN, tr⟩ := hX t tX
  have pb : bit j p = β := (bit_of_mod_succ hpm).trans (fX 0).2
  have pr : p % 2 ^ j = r := (mod_of_mod_succ hpm).trans (fr 0)
  have pN : p < N := hpt.trans tN
  by_cases hpX : p ∈ X
  · have := tri s p t sX hpX tX bs pb bt hsp hpt
    linarith
  · have e1 := S.ha1 j s p q hsp pN qN (sr.trans pr.symm) (sr.trans qr.symm) bs pb hqb
    have e2 := S.ha1 j p t q hpt tN qN (pr.trans tr.symm) (pr.trans qr.symm) pb bt hqb
    have hmem := hG s t q p hE e1 e2
    refine hempty p pN pr hpX (convexHull_mono ?_ hmem)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨s, sX, rfl⟩
    · exact ⟨t, tX, rfl⟩
    · exact ⟨q, hq, rfl⟩

/-! ### Putting it together -/

/-- The `i`-th Horton point `(i, y i)`. -/
noncomputable def pt (B : ℝ) (i : ℕ) : ℝ² := !₂[(i : ℝ), y B i]

lemma det_pt (B : ℝ) (a b c : ℕ) : det (pt B a) (pt B b) (pt B c) = D B a b c := by
  simp [det, pt, D]

lemma pt_injective (B : ℝ) : Function.Injective (pt B) := by
  intro i j h
  have := congrArg (fun p : ℝ² => p 0) h
  simpa [pt] using this

/-- The Horton set of `n` points. -/
noncomputable def horton (n : ℕ) : Finset ℝ² :=
  (Finset.range n).image (pt (2 * (n : ℝ) + 3))

lemma sys0 (N : ℕ) : Sys N 0 (D (2 * (N : ℝ) + 3)) where
  hβ := by norm_num
  cyc := D_cyc _
  anti := D_anti _
  ha1 := fun j a b c hab hb hc h1 h2 ba bb bc =>
    (HA le_rfl j a b c hab hb hc h1 h2 (ba.trans bb.symm) (by rw [ba]; exact bc)).1 ba
  ha2 := fun j a b c hab hb hc h1 h2 ba bb bc => by
    have := bit_lt j a
    have := bit_lt j b
    exact (HA le_rfl j a b c hab hb hc h1 h2 (by omega) (by omega)).2 (by omega)

lemma sys1 (N : ℕ) : Sys N 1 (fun a b c => - D (2 * (N : ℝ) + 3) a b c) where
  hβ := by norm_num
  cyc := fun a b c => by rw [D_cyc]
  anti := fun a b c => by rw [D_anti]
  ha1 := fun j a b c hab hb hc h1 h2 ba bb bc => by
    have := (HA le_rfl j a b c hab hb hc h1 h2 (ba.trans bb.symm) (by rw [ba]; exact bc)).2 ba
    linarith
  ha2 := fun j a b c hab hb hc h1 h2 ba bb bc => by
    have := bit_lt j a
    have := bit_lt j b
    have := (HA le_rfl j a b c hab hb hc h1 h2 (by omega) (by omega)).1 (by omega)
    linarith

/-- **No 7-hole in any class of the Horton set.** -/
theorem no_hole (N : ℕ) : ∀ (k j : ℕ), N ≤ j + k → ∀ (r : ℕ) (X : Finset ℕ),
    (∀ i ∈ X, i < N ∧ i % 2 ^ j = r) → X.card = 7 →
    ConvexIndep (pt (2 * (N : ℝ) + 3) '' (X : Set ℕ)) →
    (∀ i, i < N → i % 2 ^ j = r → i ∉ X →
      pt (2 * (N : ℝ) + 3) i ∉ convexHull ℝ (pt (2 * (N : ℝ) + 3) '' (X : Set ℕ))) → False := by
  intro k
  induction k with
  | zero =>
    intro j hN r X hX hcard _ _
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < X.card)
    exact hab (eq_of_mod_eq_of_le (by omega) (hX a ha).1 (hX b hb).1
      ((hX a ha).2.trans (hX b hb).2.symm))
  | succ k ih =>
    intro j hN r X hX hcard hconv hempty
    -- if all of `X` is in one half, descend
    have down : ∀ β, (∀ i ∈ X, bit j i = β) → False := by
      intro β hβ
      obtain ⟨x0, hx0⟩ := Finset.card_pos.1 (by omega : 0 < X.card)
      exact ih (j + 1) (by omega) (x0 % 2 ^ (j + 1)) X
        (fun i hi => ⟨(hX i hi).1, mod_succ_eq ((hX i hi).2.trans (hX x0 hx0).2.symm)
          ((hβ i hi).trans (hβ x0 hx0).symm)⟩) hcard hconv
        (fun i hiN him hiX => hempty i hiN ((mod_of_mod_succ him).trans (hX x0 hx0).2) hiX)
    by_cases h0 : ∀ i ∈ X, bit j i = 0
    · exact down 0 h0
    by_cases h1 : ∀ i ∈ X, bit j i = 1
    · exact down 1 h1
    push Not at h0 h1
    obtain ⟨q0, hq0, hb0⟩ := h0
    obtain ⟨q1, hq1, hb1⟩ := h1
    have hsum := Finset.card_filter_add_card_filter_not (s := X) (fun i => bit j i = 0)
    have hfil : X.filter (fun i => ¬ bit j i = 0) = X.filter (fun i => bit j i = 1) := by
      apply Finset.filter_congr
      intro i _
      have := bit_lt j i
      omega
    rw [hfil, hcard] at hsum
    rcases le_or_gt 4 (X.filter (fun i => bit j i = 0)).card with h | h
    · exact mixed (sys0 N) _ (pt_injective _)
        (fun a b q m e1 e2 e3 => mem_convexHull_triple (by rwa [det_pt]) (by rwa [det_pt])
          (by rwa [det_pt]))
        j r X hX hconv hempty h q0 hq0 hb0
    · exact mixed (sys1 N) _ (pt_injective _)
        (fun a b q m e1 e2 e3 => mem_convexHull_triple_neg (by rw [det_pt]; linarith)
          (by rw [det_pt]; linarith) (by rw [det_pt]; linarith))
        j r X hX hconv hempty (by omega) q1 hq1 hb1

/-! ### The theorem -/

/-- **Erdős Problem 216, negative answer for `k = 7` (Horton).**  For every `n` there are
`n` points in the plane, no three on a line, with no empty convex 7-gon.  Hence `g(7)`
does not exist. -/
theorem erdos_216 :
    ∀ n : ℕ, ∃ P : Finset ℝ², P.card = n ∧ NonTrilinear (P : Set ℝ²) ∧
      ¬ HasEmptyKGon 7 (P : Set ℝ²) := by
  intro n
  refine ⟨horton n, ?_, ?_, ?_⟩
  · rw [horton, Finset.card_image_of_injective _ (pt_injective _), Finset.card_range]
  · intro x hx y' hy z hz hxy hyz hxz hcol
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hz)
    have h0 := det_eq_zero_of_collinear hcol
    rw [det_pt] at h0
    exact D_ne_zero le_rfl n 0 (by omega) a b c (Finset.mem_range.1 ha) (Finset.mem_range.1 hb)
      (Finset.mem_range.1 hc) (fun h => hxy (h ▸ rfl)) (fun h => hyz (h ▸ rfl))
      (fun h => hxz (h ▸ rfl)) (by omega) (by omega) h0
  · rintro ⟨S, hcard, hSP, hconv, hempty⟩
    classical
    set X := (Finset.range n).filter (fun i => pt (2 * (n : ℝ) + 3) i ∈ S) with hXdef
    have himg : pt (2 * (n : ℝ) + 3) '' (X : Set ℕ) = (S : Set ℝ²) := by
      ext p
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
      · intro hp
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 (hSP hp))
        exact ⟨i, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hi, hp⟩), rfl⟩
    have hXS : X.image (pt (2 * (n : ℝ) + 3)) = S :=
      Finset.coe_injective (by rw [Finset.coe_image]; exact himg)
    have hXcard : X.card = 7 := by
      rw [← hcard, ← hXS, Finset.card_image_of_injective _ (pt_injective _)]
    refine no_hole n n 0 (by omega) 0 X ?_ hXcard (by rw [himg]; exact hconv) ?_
    · intro i hi
      exact ⟨Finset.mem_range.1 (Finset.mem_filter.1 hi).1, by simp [Nat.mod_one]⟩
    · intro i hiN _ hiX
      rw [himg]
      refine hempty _ ⟨?_, ?_⟩
      · exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hiN, rfl⟩)
      · intro hS
        exact hiX (Finset.mem_filter.2 ⟨Finset.mem_range.2 hiN, hS⟩)

/-- **Erdős Problem 216 for all `k ≥ 7`.**  An empty convex `k`-gon contains an empty convex
7-gon (take any 7 of its vertices), so `g(k)` does not exist for any `k ≥ 7`. -/
theorem erdos_216_of_seven_le (k : ℕ) (hk : 7 ≤ k) :
    ∀ n : ℕ, ∃ P : Finset ℝ², P.card = n ∧ NonTrilinear (P : Set ℝ²) ∧
      ¬ HasEmptyKGon k (P : Set ℝ²) := by
  intro n
  obtain ⟨P, hn, hgp, hno⟩ := erdos_216 n
  refine ⟨P, hn, hgp, ?_⟩
  rintro ⟨S, hcard, hSP, hconv, hempty⟩
  obtain ⟨T, hTS, hT7⟩ := Finset.exists_subset_card_eq (by omega : 7 ≤ S.card)
  have hTS' : (T : Set ℝ²) ⊆ S := Finset.coe_subset.2 hTS
  refine hno ⟨T, hT7, hTS'.trans hSP, ?_, ?_⟩
  · intro a ha h
    exact hconv a (hTS' ha) (convexHull_mono (Set.sdiff_subset_sdiff_left hTS') h)
  · rintro p ⟨hpP, hpT⟩ h
    by_cases hpS : p ∈ (S : Set ℝ²)
    · have hsub : (T : Set ℝ²) ⊆ (S : Set ℝ²) \ {p} := fun x hx =>
        ⟨hTS' hx, fun e => hpT (by rw [Set.mem_singleton_iff] at e; exact e ▸ hx)⟩
      exact hconv p hpS (convexHull_mono hsub h)
    · exact hempty p ⟨hpP, hpS⟩ (convexHull_mono hTS' h)

/-! ### The statement in terms of `g(k)`

`cardSet k` is the set of `N` such that every `N` points in general position contain an empty
convex `k`-gon; `g(k)` exists iff it is nonempty.  This is the form used for the statement of
this problem proposed for google-deepmind/formal-conjectures. -/

/-- The set of `N` such that any `N` points in the plane, no three on a line, contain an
empty convex `k`-gon. -/
def cardSet (k : ℕ) : Set ℕ :=
  {N | ∀ pts : Finset ℝ², pts.card = N → NonTrilinear (pts : Set ℝ²) →
    HasEmptyKGon k (pts : Set ℝ²)}

/-- `g(k)` does not exist for `k ≥ 7`. -/
theorem cardSet_eq_empty (k : ℕ) (hk : 7 ≤ k) : cardSet k = ∅ := by
  ext N
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hN
  obtain ⟨P, hc, hgp, hno⟩ := erdos_216_of_seven_le k hk N
  exact hno (hN P hc hgp)

/-- It is not the case that `g(k)` exists for every `k`. -/
theorem not_forall_cardSet_nonempty : ¬ ∀ k : ℕ, (cardSet k).Nonempty := by
  intro h
  obtain ⟨N, hN⟩ := h 7
  rw [cardSet_eq_empty 7 le_rfl] at hN
  exact hN

end Erdos216

#print axioms Erdos216.erdos_216
#print axioms Erdos216.erdos_216_of_seven_le
#print axioms Erdos216.not_forall_cardSet_nonempty
