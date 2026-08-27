/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QHarm.Basic
import QHarm.Legendre

/-!
# `QHarm.Pade` — Van Assche's Padé/Stieltjes identity, his equation (22)

With `q = t⁻¹` and `z = t^n` the Stieltjes function is `f(z) = ∑_{k≥0} q^k/(z − q^k)` and the
identity to be proved is

    P_n(z)·f(z) − Q_n(z) = ∑_{k≥0} q^k · P_n(q^k) / (z − q^k).

Because of design decision **D5**, `QHarm/Legendre.lean` *defines* `Q_n` as the expanded
form of `∑_k q^k (P_n(z) − P_n(q^k))/(z − q^k)`, so (22) is an add-and-subtract rather than a
q-series theorem. The two pieces of work are therefore

* identifying `f(t^n)` with the tail `S t − headSum t n` of the q-harmonic series
  (`stieltjes_eq_tail`), and
* reconciling the finite double sum that *defines* `legQval` with that series
  (`legQval_eq_tsum`) — Lagrange-free: `geom_sum₂_mul` for `(z^j − x^j)/(z − x)`, then one
  `tsum`/`Finset.sum` exchange and one geometric evaluation.

## Consumes

* `QHarm/Basic.lean` — `S`, `S_sub_head`, `summable_nat`;
* `QHarm/Legendre.lean` — `legCoef`, `legG`, `legVal`, `legGamma`, `legQval`, `headSum`,
  and the `n = 0` base values.

## Main results

* `latVal`, `rem` — `P_n` at the lattice point `q^k`, and the Padé remainder;
* `pade_den_pos` — positivity of the denominators `t^n − q^k` for `n ≥ 1`;
* `summable_stieltjes`, `summable_rem`, `summable_qterm` — the three geometric-comparison
  summability side conditions, all valid for every `n : ℕ` (including `n = 0`, where the
  `k = 0` denominator vanishes and Lean's `x / 0 = 0` makes that term harmless);
* `stieltjes_eq_tail` — `∑'_k q^k/(t^n − q^k) = S t − headSum t n` for `n ≥ 1`;
* `legQval_eq_tsum` — `Q_n` in series form, for every `n`;
* `pade` — **Van Assche (22)**.

## What is NOT here

* orthogonality of `legG` (`QHarm/Orthogonality.lean`);
* the sum-of-squares identity (34) and the nonvanishing of `P_n(t^n)` it yields;
* integrality of `D_n · legVal` and `D_n · legQval` (`QHarm/Integrality.lean`), and the
  clearing factor `D_n` itself (`QHarm/Clearing.lean`);
* the size bounds on `legVal` and on `rem`, and the final assembly into `A_n`, `B_n`
  (`QHarm/Forms.lean`, `QHarm/Main.lean`).
-/

namespace QHarm

/-! ### Elementary facts about `q = t⁻¹` -/

section Elementary

variable {t : ℝ}

private theorem t_pos (ht : 1 < t) : 0 < t := lt_trans zero_lt_one ht

private theorem q_nonneg (ht : 1 < t) : (0 : ℝ) ≤ t⁻¹ := le_of_lt (inv_pos.mpr (t_pos ht))

private theorem q_lt_one (ht : 1 < t) : t⁻¹ < 1 := by
  have h0 : (0 : ℝ) < t := t_pos ht
  rw [← one_div, div_lt_one h0]
  linarith

/-- The Padé denominators `t^n − q^k` are strictly positive as soon as `n ≥ 1`. -/
theorem pade_den_pos {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    0 < t ^ n - t⁻¹ ^ k := by
  have h1 : t⁻¹ ^ k ≤ 1 := pow_le_one₀ (q_nonneg ht) (q_lt_one ht).le
  have h2 : (1 : ℝ) < t ^ n := one_lt_pow₀ ht (by omega)
  linarith

end Elementary

/-! ### The definitions this file exports -/

-- `latVal` now lives in QHarm/Legendre.lean (lifted at integration).

/-- The remainder of the Padé approximation. -/
noncomputable def rem (t : ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, (t⁻¹) ^ k * latVal t n k / (t ^ n - (t⁻¹) ^ k)

/-! ### Summability

Everything is dominated by a geometric series: the numerators carry a factor `q^k` and the
reciprocal denominators are bounded uniformly in `k`. The bound is deliberately crude — the
construction has `≈ n²` powers of `t` of slack. -/

/-- A uniform-in-`k` bound for `|(t^n − q^k)⁻¹|`. At `n = 0, k = 0` the denominator really is
zero, but then `(0 : ℝ)⁻¹ = 0` and the bound is trivially true; that is the only reason this
is stated for all `n` rather than for `n ≥ 1`. -/
private noncomputable def denBd (t : ℝ) (n : ℕ) : ℝ := (t ^ n - 1)⁻¹ + (1 - t⁻¹)⁻¹

private theorem denBd_nonneg {t : ℝ} (ht : 1 < t) (n : ℕ) : 0 ≤ denBd t n := by
  have hpn : (1 : ℝ) ≤ t ^ n := one_le_pow₀ ht.le
  have hA : (0 : ℝ) ≤ (t ^ n - 1)⁻¹ := inv_nonneg.mpr (by linarith)
  have hB : (0 : ℝ) < (1 - t⁻¹)⁻¹ := inv_pos.mpr (by linarith [q_lt_one ht])
  simp only [denBd]
  linarith

private theorem abs_inv_den_le {t : ℝ} (ht : 1 < t) (n k : ℕ) :
    |(t ^ n - t⁻¹ ^ k)⁻¹| ≤ denBd t n := by
  have hq0 : (0 : ℝ) ≤ t⁻¹ := q_nonneg ht
  have hq1 : t⁻¹ < 1 := q_lt_one ht
  have hpn : (1 : ℝ) ≤ t ^ n := one_le_pow₀ ht.le
  have hA : (0 : ℝ) ≤ (t ^ n - 1)⁻¹ := inv_nonneg.mpr (by linarith)
  have hB : (0 : ℝ) < (1 - t⁻¹)⁻¹ := inv_pos.mpr (by linarith)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [denBd, pow_zero, sub_self, inv_zero, abs_zero]
      linarith
    · have hpk : t⁻¹ ^ k ≤ t⁻¹ := by
        calc t⁻¹ ^ k ≤ t⁻¹ ^ 1 := pow_le_pow_of_le_one hq0 hq1.le hk
          _ = t⁻¹ := pow_one _
      have hD : (0 : ℝ) < t ^ 0 - t⁻¹ ^ k := by
        simp only [pow_zero]; linarith
      have hle : (t ^ 0 - t⁻¹ ^ k)⁻¹ ≤ (1 - t⁻¹)⁻¹ := by
        have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 - t⁻¹ by linarith)
          (show (1 : ℝ) - t⁻¹ ≤ t ^ 0 - t⁻¹ ^ k by simp only [pow_zero]; linarith)
        rwa [one_div, one_div] at h
      rw [abs_of_nonneg (inv_nonneg.mpr hD.le)]
      simp only [denBd]
      linarith
  · have hD : (0 : ℝ) < t ^ n - t⁻¹ ^ k := pade_den_pos ht hn k
    have hpk : t⁻¹ ^ k ≤ 1 := pow_le_one₀ hq0 hq1.le
    have hDpos : (0 : ℝ) < t ^ n - 1 := by
      have : (1 : ℝ) < t ^ n := one_lt_pow₀ ht (by omega)
      linarith
    have hle : (t ^ n - t⁻¹ ^ k)⁻¹ ≤ (t ^ n - 1)⁻¹ := by
      have h := one_div_le_one_div_of_le hDpos
        (show t ^ n - 1 ≤ t ^ n - t⁻¹ ^ k by linarith)
      rwa [one_div, one_div] at h
    rw [abs_of_nonneg (inv_nonneg.mpr hD.le)]
    simp only [denBd]
    linarith

/-- The one summability workhorse: a bounded numerator against the geometric factor `q^k`. -/
private theorem summable_master {t : ℝ} (ht : 1 < t) (n : ℕ) {g : ℕ → ℝ} {M : ℝ}
    (hg : ∀ k, |g k| ≤ M) :
    Summable (fun k : ℕ => t⁻¹ ^ k * g k / (t ^ n - t⁻¹ ^ k)) := by
  have hq0 : (0 : ℝ) ≤ t⁻¹ := q_nonneg ht
  have hq1 : t⁻¹ < 1 := q_lt_one ht
  have hM : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hg 0)
  refine Summable.of_norm_bounded
    (Summable.mul_left (M * denBd t n) (summable_geometric_of_lt_one hq0 hq1)) ?_
  intro k
  have hk0 : (0 : ℝ) ≤ t⁻¹ ^ k := pow_nonneg hq0 k
  have h1 : |g k| * |(t ^ n - t⁻¹ ^ k)⁻¹| ≤ M * denBd t n :=
    mul_le_mul (hg k) (abs_inv_den_le ht n k) (abs_nonneg _) hM
  calc ‖t⁻¹ ^ k * g k / (t ^ n - t⁻¹ ^ k)‖
      = t⁻¹ ^ k * (|g k| * |(t ^ n - t⁻¹ ^ k)⁻¹|) := by
        rw [Real.norm_eq_abs, div_eq_mul_inv, abs_mul, abs_mul, abs_of_nonneg hk0, mul_assoc]
    _ ≤ t⁻¹ ^ k * (M * denBd t n) := mul_le_mul_of_nonneg_left h1 hk0
    _ = M * denBd t n * t⁻¹ ^ k := by ring

/-- The crude uniform bound on the lattice values: `|w_k| ≤ 1`, so `|P_n(q^k)|` is at most the
sum of the absolute values of the coefficients — a constant in `k`, which is all that is
needed. -/
private noncomputable def coefAbsSum (t : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), |legCoef t n j|

private theorem abs_latVal_le {t : ℝ} (ht : 1 < t) (n k : ℕ) :
    |latVal t n k| ≤ coefAbsSum t n := by
  have hq0 : (0 : ℝ) ≤ t⁻¹ := q_nonneg ht
  have hq1 : t⁻¹ < 1 := q_lt_one ht
  have hinv0 : (0 : ℝ) ≤ ((t : ℝ) ^ n)⁻¹ := by rw [← inv_pow]; exact pow_nonneg hq0 n
  have hinv1 : ((t : ℝ) ^ n)⁻¹ ≤ 1 := by rw [← inv_pow]; exact pow_le_one₀ hq0 hq1.le
  have hw0 : (0 : ℝ) ≤ t⁻¹ ^ k * (t ^ n)⁻¹ := mul_nonneg (pow_nonneg hq0 k) hinv0
  have hw1 : t⁻¹ ^ k * (t ^ n)⁻¹ ≤ 1 := mul_le_one₀ (pow_le_one₀ hq0 hq1.le) hinv0 hinv1
  unfold latVal legG coefAbsSum
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro j _
  rw [abs_mul]
  have hpj : |(t⁻¹ ^ k * (t ^ n)⁻¹) ^ j| ≤ 1 := by
    rw [abs_pow, abs_of_nonneg hw0]
    exact pow_le_one₀ hw0 hw1
  calc |legCoef t n j| * |(t⁻¹ ^ k * (t ^ n)⁻¹) ^ j| ≤ |legCoef t n j| * 1 :=
        mul_le_mul_of_nonneg_left hpj (abs_nonneg _)
    _ = |legCoef t n j| := mul_one _

theorem summable_stieltjes {t : ℝ} (ht : 1 < t) (n : ℕ) :
    Summable (fun k : ℕ => (t⁻¹) ^ k / (t ^ n - (t⁻¹) ^ k)) := by
  have h := summable_master ht n (g := fun _ : ℕ => (1 : ℝ)) (M := 1) (fun k => by simp)
  exact h.congr (fun k => by rw [mul_one])

theorem summable_rem {t : ℝ} (ht : 1 < t) (n : ℕ) :
    Summable (fun k : ℕ => (t⁻¹) ^ k * latVal t n k / (t ^ n - (t⁻¹) ^ k)) :=
  summable_master ht n (abs_latVal_le ht n)

theorem summable_qterm {t : ℝ} (ht : 1 < t) (n : ℕ) :
    Summable (fun k : ℕ => (t⁻¹) ^ k * (legVal t n - latVal t n k) / (t ^ n - (t⁻¹) ^ k)) := by
  refine summable_master ht n (M := |legVal t n| + coefAbsSum t n) (fun k => ?_)
  have h1 : |legVal t n - latVal t n k| ≤ |legVal t n| + |latVal t n k| := by
    have h := abs_add_le (legVal t n) (-(latVal t n k))
    rwa [← sub_eq_add_neg, abs_neg] at h
  linarith [abs_latVal_le ht n k]

/-! ### The Stieltjes function is the tail of the q-harmonic series

`q^k/(t^n − q^k) = 1/(t^{n+k} − 1)` — multiply numerator and denominator by `t^k`. -/

private theorem stieltjes_term {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    t⁻¹ ^ k / (t ^ n - t⁻¹ ^ k) = 1 / (t ^ (k + n) - 1) := by
  have ht0 : (0 : ℝ) < t := t_pos ht
  have hD : (0 : ℝ) < t ^ n - t⁻¹ ^ k := pade_den_pos ht hn k
  have hE : (0 : ℝ) < t ^ (k + n) - 1 := by
    have : (1 : ℝ) < t ^ (k + n) := one_lt_pow₀ ht (by omega)
    linarith
  have hq : t⁻¹ ^ k * t ^ k = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt ht0), one_pow]
  have hx : t⁻¹ ^ k * t ^ (k + n) = t ^ n := by
    rw [pow_add, ← mul_assoc, hq, one_mul]
  rw [div_eq_div_iff (ne_of_gt hD) (ne_of_gt hE)]
  linear_combination hx

/-- The Stieltjes function at `z = t^n` is exactly the tail of the q-harmonic series. -/
theorem stieltjes_eq_tail {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) :
    ∑' k : ℕ, (t⁻¹) ^ k / (t ^ n - (t⁻¹) ^ k) = S t - headSum t n := by
  simp only [headSum]
  rw [S_sub_head ht (n - 1)]
  refine tsum_congr (fun k => ?_)
  rw [stieltjes_term ht hn k, show k + (n - 1) + 1 = k + n from by omega]

/-! ### `Q_n` in series form -/

/-- `P_n(t^n) − P_n(q^k) = ∑_j γ_{n,j} ((t^n)^j − (q^k)^j)`: the add-and-subtract, written in
the `legGamma` normalisation (that is what `legGamma` exists for). -/
private theorem legVal_sub_latVal {t : ℝ} (ht : 1 < t) (n k : ℕ) :
    legVal t n - latVal t n k
      = ∑ j ∈ Finset.range (n + 1), legGamma t n j * ((t ^ n) ^ j - (t⁻¹ ^ k) ^ j) := by
  have ht0 : (0 : ℝ) < t := t_pos ht
  have hz : ((t : ℝ) ^ n) ≠ 0 := ne_of_gt (pow_pos ht0 n)
  rw [legVal_eq]
  simp only [latVal, legG]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hzj : (((t : ℝ) ^ n) ^ j) ≠ 0 := pow_ne_zero _ hz
  have h1 : legGamma t n j * ((t ^ n) ^ j) = legCoef t n j := by
    rw [legGamma, mul_assoc, inv_mul_cancel₀ hzj, mul_one]
  have h2 : legGamma t n j * ((t⁻¹ ^ k) ^ j)
      = legCoef t n j * (t⁻¹ ^ k * (t ^ n)⁻¹) ^ j := by
    rw [legGamma, mul_pow, inv_pow]
    ring
  rw [mul_sub, h1, h2]

/-- The `k`-th `Q_n` summand, expanded by `geom_sum₂_mul`. -/
private theorem qterm_eq {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    t⁻¹ ^ k * (legVal t n - latVal t n k) / (t ^ n - t⁻¹ ^ k)
      = ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range j,
          legGamma t n j * (t ^ n) ^ i * (t⁻¹ ^ (j - i)) ^ k := by
  have hD : (0 : ℝ) < t ^ n - t⁻¹ ^ k := pade_den_pos ht hn k
  have hswap : ∀ j i : ℕ, ((t : ℝ)⁻¹ ^ (j - i)) ^ k = (t⁻¹ ^ k) ^ (j - i) := by
    intro j i
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [div_eq_iff (ne_of_gt hD), legVal_sub_latVal ht n k, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [hswap]
  have hfac : (∑ i ∈ Finset.range j, legGamma t n j * (t ^ n) ^ i * (t⁻¹ ^ k) ^ (j - i))
      = legGamma t n j * t⁻¹ ^ k
          * ∑ i ∈ Finset.range j, ((t : ℝ) ^ n) ^ i * (t⁻¹ ^ k) ^ (j - 1 - i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hij : i < j := Finset.mem_range.mp hi
    have hpow : ((t : ℝ)⁻¹ ^ k) ^ (j - i) = t⁻¹ ^ k * (t⁻¹ ^ k) ^ (j - 1 - i) := by
      rw [show j - i = (j - 1 - i) + 1 from by omega, pow_succ]
      ring
    rw [hpow]
    ring
  rw [hfac, mul_assoc (legGamma t n j * t⁻¹ ^ k), geom_sum₂_mul]
  ring

private theorem geom_inv_eval {t : ℝ} (ht : 1 < t) {m : ℕ} (hm : 1 ≤ m) :
    (1 - t⁻¹ ^ m)⁻¹ = t ^ m / (t ^ m - 1) := by
  have hu : (1 : ℝ) < t ^ m := one_lt_pow₀ ht (by omega)
  have hu0 : (0 : ℝ) < t ^ m := by linarith
  rw [inv_pow, show (1 : ℝ) - ((t : ℝ) ^ m)⁻¹ = (t ^ m - 1) / t ^ m from by field_simp, inv_div]

/-- `Q_n` in series form — the reconciliation of the finite double sum with the
add-and-subtract. -/
theorem legQval_eq_tsum {t : ℝ} (ht : 1 < t) (n : ℕ) :
    legQval t n
      = ∑' k : ℕ, (t⁻¹) ^ k * (legVal t n - latVal t n k) / (t ^ n - (t⁻¹) ^ k) := by
  have hq0 : (0 : ℝ) ≤ t⁻¹ := q_nonneg ht
  have hq1 : t⁻¹ < 1 := q_lt_one ht
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hz : ∀ k : ℕ,
        (t⁻¹) ^ k * (legVal t 0 - latVal t 0 k) / (t ^ 0 - (t⁻¹) ^ k) = 0 := by
      intro k
      simp only [latVal, legG_zero, legVal_zero, sub_self, mul_zero, zero_div]
    rw [tsum_congr hz, tsum_zero, legQval_zero]
  · have hgeo : ∀ j i : ℕ, i < j → Summable (fun k : ℕ =>
        legGamma t n j * (t ^ n) ^ i * ((t : ℝ)⁻¹ ^ (j - i)) ^ k) := by
      intro j i hij
      exact Summable.mul_left _ (summable_geometric_of_lt_one
        (pow_nonneg hq0 _) (pow_lt_one₀ hq0 hq1 (by omega)))
    have hsumj : ∀ j ∈ Finset.range (n + 1), Summable (fun k : ℕ =>
        ∑ i ∈ Finset.range j, legGamma t n j * (t ^ n) ^ i * ((t : ℝ)⁻¹ ^ (j - i)) ^ k) := by
      intro j _
      exact summable_sum (fun i hi => hgeo j i (Finset.mem_range.mp hi))
    have hstep : ∀ j ∈ Finset.range (n + 1),
        (∑' k : ℕ, ∑ i ∈ Finset.range j,
            legGamma t n j * (t ^ n) ^ i * ((t : ℝ)⁻¹ ^ (j - i)) ^ k)
          = legGamma t n j *
              ∑ i ∈ Finset.range j, (t ^ n) ^ i * (t ^ (j - i) / (t ^ (j - i) - 1)) := by
      intro j _
      rw [Summable.tsum_finsetSum (fun i hi => hgeo j i (Finset.mem_range.mp hi)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hij : i < j := Finset.mem_range.mp hi
      rw [tsum_mul_left, tsum_geometric_of_lt_one (pow_nonneg hq0 _)
        (pow_lt_one₀ hq0 hq1 (by omega)), geom_inv_eval ht (by omega : 1 ≤ j - i)]
      ring
    simp only [legQval]
    rw [tsum_congr (qterm_eq ht hn), Summable.tsum_finsetSum hsumj]
    exact (Finset.sum_congr rfl hstep).symm

/-! ### Van Assche (22) -/

/-- **Van Assche (22).** -/
theorem pade {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) :
    legVal t n * (S t - headSum t n) - legQval t n = rem t n := by
  have h1 : Summable (fun k : ℕ => legVal t n * ((t⁻¹) ^ k / (t ^ n - (t⁻¹) ^ k))) :=
    Summable.mul_left _ (summable_stieltjes ht n)
  have h2 := summable_qterm ht n
  rw [← stieltjes_eq_tail ht hn, legQval_eq_tsum ht n]
  simp only [rem]
  rw [← tsum_mul_left, ← Summable.tsum_sub h1 h2]
  refine tsum_congr (fun k => ?_)
  have hD : (t : ℝ) ^ n - t⁻¹ ^ k ≠ 0 := ne_of_gt (pade_den_pos ht hn k)
  field_simp
  ring

end QHarm

#print axioms QHarm.pade
#print axioms QHarm.legQval_eq_tsum
#print axioms QHarm.stieltjes_eq_tail
#print axioms QHarm.summable_stieltjes
#print axioms QHarm.summable_rem
#print axioms QHarm.summable_qterm
