/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QHarm.Legendre

/-!
# QHarm/CoefBound.lean — crude `n`-uniform size bounds on the little q-Legendre data

## Consumes

* `QHarm/Legendre.lean` — `legCoef`, `legG`, `legGamma` (definitions).
* `QHarm/QBinom.lean` — `gauss`, `gaussConst`, `gauss_pos`, `gauss_le_const_mul_pow`.

Nothing else. Every statement below is proved outright; there are **no frontiers** in this
file.

## Main results

All bounds are deliberately lossy and every exponent is a natural number — no inverses.
`gaussConst t = exp (t/(t-1)^2)` is the `n`- and `k`-uniform constant from `QBinom`.

* `gammaExp n j = C(j,2) + j*(n-j)` — the exponent that actually controls `legGamma`.
  `gammaExp_le_mul : gammaExp n j ≤ n*j` and `gammaExp_le_choose : gammaExp n j ≤ C(n,2)`
  (the second is sharp: equality at `j = n` and `j = n-1`).
* `abs_legCoef_le_aux : |legCoef t n j| ≤ gaussConst t ^ 2 * (t ^ gammaExp n j * t ^ (n*j))`
  — the sharp form of the coefficient bound, from which everything else is a weakening.
* `abs_legCoef_le : |legCoef t n j| ≤ gaussConst t ^ 2 * t ^ (2*n*j)`.
* `abs_legGamma_le_gammaExp : |legGamma t n j| ≤ gaussConst t ^ 2 * t ^ gammaExp n j`,
  with the weakenings `abs_legGamma_le` (`t ^ (n*j)`) and
  `abs_legGamma_le_choose` (`t ^ (n.choose 2)`, **uniform in `j`**).
* `latVal t n k = legG t n ((t⁻¹)^k * (t^n)⁻¹) = P_n(q^k | 1/t)` — the lattice values.
  `latVal_eq` rewrites it as `∑_j legGamma t n j * ((t⁻¹)^k)^j`.
* `abs_latVal_le : |latVal t n k| ≤ (n+1) * gaussConst t ^ 2 * t ^ (n.choose 2)`,
  **uniform in `k`**. See the honesty note below — this exponent is `n(n-1)/2`, not `0`.
* `summable_weight_abs_latVal`, `summable_weight_sq_latVal` — the two weighted series
  `∑_k (t⁻¹)^k |P_n(q^k)|` and `∑_k (t⁻¹)^k P_n(q^k)^2` converge, by comparison with the
  geometric series through `abs_latVal_le`.
* `sum_abs_latVal_le` — **Cauchy–Schwarz**: given any bound `h` on the weighted square sum,
  `∑'_k (t⁻¹)^k |P_n(q^k)| ≤ √((1 - t⁻¹)⁻¹) * √h`. The squared-norm bound is taken as a
  hypothesis; it is owned by `QHarm/Orthogonality.lean`.

## Honesty note on the exponent in `abs_latVal_le`

The triangle inequality cannot see the cancellation in `∑_j legGamma t n j x^j`. The
individual terms really are as large as `t^{n(n-1)/2}` (the maximum of `gammaExp n j` over
`j ≤ n`, attained at `j = n` and `j = n-1`), while the true value satisfies
`|P_n(q^k)| < 1` for every `k` — measured exactly with `Fraction`s at `t ∈ {2,3}`,
`n ≤ 8`, `k ≤ 40`: `sup_k |P_n(q^k)| = 1`, approached as `k → ∞` since `P_n(0) = 1`.
So `abs_latVal_le` overshoots the truth by exactly `t^{n(n-1)/2}` and **must not** be used
where that factor matters; it is here only to supply summability. The quantity the
assembly needs, `∑_k (t⁻¹)^k |P_n(q^k)|`, is obtained instead from `sum_abs_latVal_le`
against the squared norm (measured: `∑_k (t⁻¹)^k P_n(q^k)^2 ≈ t^{-n}`, so Cauchy–Schwarz
delivers `t^{-n/2}` up to a constant).

## What is NOT here

* Orthogonality and the squared-norm evaluation — `QHarm/Orthogonality.lean`.
* Any lower bound on `legVal` / dominant-term separation — `QHarm/Degree.lean`.
* Integrality of the cleared forms — `QHarm/Integrality.lean`.
* The clearing factor `D_n` — `QHarm/Clearing.lean`.
* The linear forms and the balance inequality — `QHarm/Forms.lean`, `QHarm/Main.lean`.
-/

namespace QHarm

open Finset

/-! ### Exponent arithmetic

Everything here is `Nat`-level bookkeeping, isolated so that no analytic proof below has to
fight `Nat` subtraction or `Nat` division. -/

/-- `2 * C(j,2) = j(j-1)` — the `Nat` division in `Nat.choose_two_right` is exact. -/
theorem two_mul_choose_two (j : ℕ) : 2 * j.choose 2 = j * (j - 1) := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self j).two_dvd]

/-- The exponent controlling `legGamma t n j`: `C(j,2) + j(n-j)`. -/
def gammaExp (n j : ℕ) : ℕ := j.choose 2 + j * (n - j)

@[simp] theorem gammaExp_zero_right (n : ℕ) : gammaExp n 0 = 0 := by simp [gammaExp]

/-- Subtraction-free companion: `2*C(j,2) + j = j^2`. This is the form the `Nat`
bookkeeping below actually uses, because `omega` handles it without atom mismatches. -/
theorem two_mul_choose_two_add (j : ℕ) : 2 * j.choose 2 + j = j * j := by
  have h := two_mul_choose_two j
  rcases j with _ | a
  · simp
  · have hred : (a + 1) * (a + 1 - 1) = (a + 1) * a := by rw [Nat.add_sub_cancel]
    have hsq : (a + 1) * (a + 1) = (a + 1) * a + (a + 1) := by ring
    omega

/-- The exact quadratic identity behind both bounds, in subtraction-free form:
`2*gammaExp n j + (n-j)^2 + j = n^2`. Everything else is a corollary. -/
theorem two_mul_gammaExp_add {n j : ℕ} (h : j ≤ n) :
    2 * gammaExp n j + (n - j) * (n - j) + j = n * n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have hsub : j + m - j = m := by omega
  have hA : 2 * j.choose 2 + j = j * j := two_mul_choose_two_add j
  have hexp : (j + m) * (j + m) = j * j + 2 * (j * m) + m * m := by ring
  unfold gammaExp
  rw [hsub]
  omega

private theorem self_le_sq (m : ℕ) : m ≤ m * m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  · exact Nat.le_mul_of_pos_left m hm

/-- `gammaExp n j ≤ n * j`. -/
theorem gammaExp_le_mul {n j : ℕ} (h : j ≤ n) : gammaExp n j ≤ n * j := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have hsub : j + m - j = m := by omega
  have hA : 2 * j.choose 2 + j = j * j := two_mul_choose_two_add j
  have h4 : (j + m) * j = j * j + j * m := by ring
  unfold gammaExp
  rw [hsub]
  omega

/-- `gammaExp n j ≤ C(n,2)`, **uniformly in `j`**. Sharp: equality at `j = n` and
`j = n - 1`. -/
theorem gammaExp_le_choose {n j : ℕ} (h : j ≤ n) : gammaExp n j ≤ n.choose 2 := by
  have hid := two_mul_gammaExp_add h
  have hB : 2 * n.choose 2 + n = n * n := two_mul_choose_two_add n
  have hm : n - j ≤ (n - j) * (n - j) := self_le_sq (n - j)
  omega

/-! ### The coefficient bounds -/

/-- **The sharp form.** Every exponent is a natural number and the constant is uniform in
both `n` and `j`. -/
theorem abs_legCoef_le_aux {t : ℝ} (ht : 1 < t) {n j : ℕ} (h : j ≤ n) :
    |legCoef t n j| ≤ gaussConst t ^ 2 * (t ^ gammaExp n j * t ^ (n * j)) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hgp1 : 0 < gauss t n j := gauss_pos ht h
  have hgp2 : 0 < gauss t (n + j) n := gauss_pos ht (Nat.le_add_right n j)
  have hC : 0 ≤ gaussConst t := le_trans zero_le_one (one_le_gaussConst ht)
  have habs : |legCoef t n j| = t ^ (j.choose 2) * gauss t n j * gauss t (n + j) n := by
    unfold legCoef
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (pow_pos ht0 (j.choose 2)), abs_of_pos hgp1, abs_of_pos hgp2]
  have hg1 : gauss t n j ≤ gaussConst t * t ^ (j * (n - j)) := gauss_le_const_mul_pow ht h
  have hg2 : gauss t (n + j) n ≤ gaussConst t * t ^ (n * j) := by
    have := gauss_le_const_mul_pow ht (Nat.le_add_right n j)
    rwa [Nat.add_sub_cancel_left] at this
  have hstep :
      t ^ (j.choose 2) * gauss t n j * gauss t (n + j) n
        ≤ t ^ (j.choose 2) * (gaussConst t * t ^ (j * (n - j))) * (gaussConst t * t ^ (n * j)) := by
    have h1 : t ^ (j.choose 2) * gauss t n j
        ≤ t ^ (j.choose 2) * (gaussConst t * t ^ (j * (n - j))) :=
      mul_le_mul_of_nonneg_left hg1 (pow_pos ht0 _).le
    have h2 : (0 : ℝ) ≤ t ^ (j.choose 2) * (gaussConst t * t ^ (j * (n - j))) := by positivity
    calc t ^ (j.choose 2) * gauss t n j * gauss t (n + j) n
        ≤ t ^ (j.choose 2) * (gaussConst t * t ^ (j * (n - j))) * gauss t (n + j) n :=
          mul_le_mul_of_nonneg_right h1 hgp2.le
      _ ≤ t ^ (j.choose 2) * (gaussConst t * t ^ (j * (n - j))) * (gaussConst t * t ^ (n * j)) :=
          mul_le_mul_of_nonneg_left hg2 h2
  refine le_trans (le_of_eq habs) (le_trans hstep (le_of_eq ?_))
  unfold gammaExp
  rw [pow_add]
  ring

/-- The bound in the shape requested by the assembly file. Lossy on purpose. -/
theorem abs_legCoef_le {t : ℝ} (ht : 1 < t) {n j : ℕ} (h : j ≤ n) :
    |legCoef t n j| ≤ gaussConst t ^ 2 * t ^ (2 * n * j) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hC : 0 ≤ gaussConst t ^ 2 := by positivity
  refine le_trans (abs_legCoef_le_aux ht h) ?_
  refine mul_le_mul_of_nonneg_left ?_ hC
  rw [← pow_add]
  refine pow_le_pow_right₀ ht.le ?_
  have h1 := gammaExp_le_mul h
  have h2 : 2 * n * j = n * j + n * j := by ring
  omega

/-- **The sharp bound on the `x`-coefficients of `P_n`.** -/
theorem abs_legGamma_le_gammaExp {t : ℝ} (ht : 1 < t) {n j : ℕ} (h : j ≤ n) :
    |legGamma t n j| ≤ gaussConst t ^ 2 * t ^ gammaExp n j := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hpow : (0 : ℝ) < t ^ (n * j) := pow_pos ht0 _
  have hrw : |legGamma t n j| = |legCoef t n j| * (t ^ (n * j))⁻¹ := by
    unfold legGamma
    rw [abs_mul, ← pow_mul, abs_of_pos (inv_pos.mpr hpow)]
  rw [hrw]
  calc |legCoef t n j| * (t ^ (n * j))⁻¹
      ≤ (gaussConst t ^ 2 * (t ^ gammaExp n j * t ^ (n * j))) * (t ^ (n * j))⁻¹ :=
        mul_le_mul_of_nonneg_right (abs_legCoef_le_aux ht h) (by positivity)
    _ = gaussConst t ^ 2 * t ^ gammaExp n j := by
        field_simp

/-- The bound in the shape requested by the assembly file. -/
theorem abs_legGamma_le {t : ℝ} (ht : 1 < t) {n j : ℕ} (h : j ≤ n) :
    |legGamma t n j| ≤ gaussConst t ^ 2 * t ^ (n * j) := by
  have hC : 0 ≤ gaussConst t ^ 2 := by positivity
  refine le_trans (abs_legGamma_le_gammaExp ht h) ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht.le (gammaExp_le_mul h)) hC

/-- The `j`-**uniform** bound: `|legGamma t n j| ≤ C^2 t^{n(n-1)/2}` for every `j ≤ n`. -/
theorem abs_legGamma_le_choose {t : ℝ} (ht : 1 < t) {n j : ℕ} (h : j ≤ n) :
    |legGamma t n j| ≤ gaussConst t ^ 2 * t ^ (n.choose 2) := by
  have hC : 0 ≤ gaussConst t ^ 2 := by positivity
  refine le_trans (abs_legGamma_le_gammaExp ht h) ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht.le (gammaExp_le_choose h)) hC

/-! ### The lattice values -/

-- `latVal` now lives in QHarm/Legendre.lean (lifted at integration).

/-- The bridging lemma: the rescaling `w = x / t^n` turns `legCoef` into `legGamma`. -/
theorem latVal_eq (t : ℝ) (n k : ℕ) :
    latVal t n k = ∑ j ∈ Finset.range (n + 1), legGamma t n j * ((t⁻¹) ^ k) ^ j := by
  unfold latVal legG legGamma
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, inv_pow]
  ring

/-- **The uniform bound on the lattice values.** Uniform in `k`; the exponent is
`n.choose 2 = n(n-1)/2`. See the honesty note in the file header: the truth is `< 1`, this
bound overshoots by exactly that factor, and it exists only to give summability. -/
theorem abs_latVal_le {t : ℝ} (ht : 1 < t) (n k : ℕ) :
    |latVal t n k| ≤ (n + 1) * gaussConst t ^ 2 * t ^ (n.choose 2) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hinv : (0 : ℝ) ≤ t⁻¹ := by positivity
  have hinv1 : t⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr ht.le
  have hterm : ∀ j ∈ Finset.range (n + 1),
      |legGamma t n j * ((t⁻¹) ^ k) ^ j| ≤ gaussConst t ^ 2 * t ^ (n.choose 2) := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hx : |((t⁻¹) ^ k) ^ j| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (by positivity) (pow_le_one₀ hinv hinv1)
    calc |legGamma t n j * ((t⁻¹) ^ k) ^ j| = |legGamma t n j| * |((t⁻¹) ^ k) ^ j| := abs_mul _ _
      _ ≤ |legGamma t n j| * 1 := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
      _ = |legGamma t n j| := mul_one _
      _ ≤ gaussConst t ^ 2 * t ^ (n.choose 2) := abs_legGamma_le_choose ht hjn
  rw [latVal_eq]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  exact le_of_eq (by ring)

/-! ### Summability of the two weighted series -/

private theorem summable_geom_inv {t : ℝ} (ht : 1 < t) :
    Summable (fun k : ℕ => (t⁻¹) ^ k) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  refine summable_geometric_of_lt_one (by positivity) ?_
  rw [inv_lt_one_iff₀]
  exact Or.inr ht

theorem summable_weight_abs_latVal {t : ℝ} (ht : 1 < t) (n : ℕ) :
    Summable (fun k : ℕ => (t⁻¹) ^ k * |latVal t n k|) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  set B : ℝ := (n + 1) * gaussConst t ^ 2 * t ^ (n.choose 2) with hB
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geom_inv ht).mul_left B)
  exact mul_le_mul_of_nonneg_left (abs_latVal_le ht n k) (by positivity)
    |>.trans (le_of_eq (by ring))

theorem summable_weight_sq_latVal {t : ℝ} (ht : 1 < t) (n : ℕ) :
    Summable (fun k : ℕ => (t⁻¹) ^ k * (latVal t n k) ^ 2) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  set B : ℝ := (n + 1) * gaussConst t ^ 2 * t ^ (n.choose 2) with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geom_inv ht).mul_left (B ^ 2))
  have h1 : (latVal t n k) ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_latVal_le ht n k) 2
  calc (t⁻¹) ^ k * (latVal t n k) ^ 2 ≤ (t⁻¹) ^ k * B ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = B ^ 2 * (t⁻¹) ^ k := by ring

/-! ### Cauchy–Schwarz against the squared norm

This is the step the final assembly actually consumes. The squared-norm bound `h` is a
hypothesis: it is owned by `QHarm/Orthogonality.lean` (the `m = n` evaluation of the same
Lagrange identity), and measured to be `≈ t^{-n}`, whence this lemma delivers `≈ t^{-n/2}`. -/

theorem sum_abs_latVal_le {t : ℝ} (ht : 1 < t) (n : ℕ) {h : ℝ}
    (hh : ∑' k : ℕ, (t⁻¹) ^ k * (latVal t n k) ^ 2 ≤ h) :
    ∑' k : ℕ, (t⁻¹) ^ k * |latVal t n k| ≤ Real.sqrt ((1 - t⁻¹)⁻¹) * Real.sqrt h := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hinv1 : t⁻¹ < 1 := by rw [inv_lt_one_iff₀]; exact Or.inr ht
  have hinv0 : (0 : ℝ) ≤ t⁻¹ := by positivity
  have hgeom : ∑' k : ℕ, (t⁻¹) ^ k = (1 - t⁻¹)⁻¹ := tsum_geometric_of_lt_one hinv0 hinv1
  refine Real.tsum_le_of_sum_le (fun k => by positivity) ?_
  intro s
  -- rewrite each summand as `√f * √g`
  have hrw : ∀ k ∈ s, (t⁻¹) ^ k * |latVal t n k|
      = Real.sqrt ((t⁻¹) ^ k) * Real.sqrt ((t⁻¹) ^ k * (latVal t n k) ^ 2) := by
    intro k _
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (t⁻¹) ^ k), Real.sqrt_sq_eq_abs, ← mul_assoc,
      Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ (t⁻¹) ^ k)]
  rw [Finset.sum_congr rfl hrw]
  refine le_trans (Real.sum_sqrt_mul_sqrt_le s (fun k => by positivity)
    (fun k => by positivity)) ?_
  have h1 : ∑ k ∈ s, (t⁻¹) ^ k ≤ (1 - t⁻¹)⁻¹ := by
    rw [← hgeom]
    exact (summable_geom_inv ht).sum_le_tsum s (fun k _ => by positivity)
  have h2 : ∑ k ∈ s, (t⁻¹) ^ k * (latVal t n k) ^ 2 ≤ h :=
    le_trans ((summable_weight_sq_latVal ht n).sum_le_tsum s (fun k _ => by positivity)) hh
  exact mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

end QHarm

#print axioms QHarm.abs_legCoef_le
#print axioms QHarm.abs_legGamma_le
#print axioms QHarm.abs_legGamma_le_choose
#print axioms QHarm.abs_latVal_le
#print axioms QHarm.sum_abs_latVal_le
