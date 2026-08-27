/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QHarm.Pade
import QHarm.Clearing
import QHarm.CoefBound
import QHarm.Orthogonality
import QHarm.Integrality

/-!
# `QHarm/Forms.lean` — the sum-of-squares form (34) and the quantitative estimate

The three results `QHarm/Main.lean` consumes from this file: Van Assche's equation (34)
(`sumsq`), its strict positivity (`sumsq_pos`, which is the whole of "nonvanishing" — see
the internal build notes deviation **D2**), and the size bound `|clr_n · R_n| → 0` (`clr_mul_rem_tendsto_zero`).

## Consumes

* `QHarm/Legendre.lean` — `legCoef`, `legG`, `legVal`, `legGamma`, `latVal`;
* `QHarm/Pade.lean` — `rem`, `pade_den_pos`;
* `QHarm/Clearing.lean` — `Dr`, `Dr_pos`, `Dr_le_gaussExp`, `gaussExp`, `two_mul_gaussExp`;
* `QHarm/CoefBound.lean` — `abs_latVal_le`, `summable_weight_abs_latVal`,
  `sum_abs_latVal_le` (Cauchy–Schwarz);
* `QHarm/Orthogonality.lean` — `orth_tsum` (the vanishing half) and `norm_sq_value`
  (the squared norm, exactly);
* `QHarm/Integrality.lean` — `Mexp` and `two_mul_Mexp_add` (the extra clearing exponent).

**There are no frontiers in this file.** Every `sorry`-free dependency listed above was on
disk and building when this file was written, so the two frontiers originally budgeted here
(`orth_tsum` and an `L`-bound) are both discharged by real theorems.

## Main results

* `sumsq` — **Van Assche (34)**: `P_n(t^n) · R_n = ∑_k q^k P_n(q^k)² / (t^n − q^k)`.
  Add-and-subtract: `P_n(t^n) = P_n(q^k) + (P_n(t^n) − P_n(q^k))`, the second piece is
  `(t^n − q^k)` times a polynomial of degree `< n` in `q^k`, and `orth_tsum` kills it
  monomial by monomial.
* `sumsq_pos` — the right-hand side is `> 0`. Every term is `≥ 0` (`pade_den_pos`), and
  some `k` has `P_n(q^k) ≠ 0` because `∑_k q^k P_n(q^k)² = t^{n+1}/(t^{2n+1} − 1) > 0`
  (`Orthogonality.norm_sq_value`). No polynomial-root counting and no limit is needed.
* `clr_mul_rem_tendsto_zero` — `|clr_n · R_n| → 0`, via
  `|clr_n · R_n| ≤ (1 − q)⁻¹ (t^n − 1)⁻¹` for every `n ≥ 1`. The three ingredients are
  `clrF t n ≤ t^{n²}` (`clrF_le`), `|R_n| ≤ t^{−n²}(t^n − 1)⁻¹ · L_n` (`abs_rem_le`), and
  `L_n := ∑_k q^k |P_n(q^k)| ≤ (1 − q)⁻¹` (`L_le`).
* `L_le` — the `n`-uniform bound on `∑_k q^k |P_n(q^k)|`, proved outright: Cauchy–Schwarz
  (`CoefBound.sum_abs_latVal_le`) against `h_n = t^{n+1}/(t^{2n+1} − 1) ≤ (1 − q)⁻¹`.
* `clrF`, `clrF_pos`, `clrF_le` — a **local restatement** of `QHarm/Main.lean`'s `clr`.
  `Main.lean` cannot be imported (it imports this file's consumers), so the definition is
  repeated here character-identically, over the *same* `Mexp` that `Main.lean` uses (from
  `QHarm/Integrality.lean`); the one-line bridge `clr = clrF` is `rfl` and belongs to the
  integration step.

## Why the geometric expansion here is finite

the internal build notes's sketch expands `1/(t^n − q^k) = t^{-n} ∑_{r≥0} (q^k t^{-n})^r` and swaps a
*double* series, which needs an absolute-convergence interchange on `ℕ × ℕ`. That is not
done here. Instead the expansion is truncated exactly:

    q^k P_n(q^k)/(t^n − q^k)
      = ∑_{r<n} t^{-n(r+1)} (q^k)^{r+1} P_n(q^k)
        + t^{-n²} (q^k)^{n+1} P_n(q^k)/(t^n − q^k)         (`split_term`)

— a finite geometric sum plus an exact remainder, so only a `Finset.sum`/`tsum` exchange is
ever needed. `orth_tsum` annihilates the `n` finite terms, and the remainder carries the
whole `t^{-n²}` by itself. This is `split_term` → `rem_eq_tail` → `abs_rem_le`.

## What is NOT here

* orthogonality itself and the squared norm — `QHarm/Orthogonality.lean`;
* the Padé identity (22) — `QHarm/Pade.lean`;
* integrality of `t^{M_n} D_n · P_n(t^n)` and of the `A_n` form — `QHarm/Integrality.lean`;
* the clearing factor `D_n` and its size — `QHarm/Clearing.lean`;
* the final assembly into `master_int` — `QHarm/Main.lean`;
* the general rational-base track (`Cyclotomic`/`Mertens`/`Growth`), not needed for the
  integer case (the internal build notes D1).
-/

namespace QHarm

open Filter

/-! ### Local restatement of `QHarm/Main.lean`'s clearing factor

`Main.lean` imports the files that import this one, so it cannot be imported here. `clrF` is
character-identical to `QHarm.clr`, over the same `Mexp` (imported from
`QHarm/Integrality.lean`), so the bridge `clr t n = clrF t n` is `rfl`. -/

/-- The full clearing factor `t^{M_n} · D_n`. Local copy of `QHarm.clr`. -/
noncomputable def clrF (t : ℝ) (n : ℕ) : ℝ := t ^ Mexp n * Dr t n

/-! ### Elementary facts about `q = t⁻¹` -/

section Elementary

variable {t : ℝ}

private theorem tpos (ht : 1 < t) : 0 < t := lt_trans zero_lt_one ht

private theorem qnn (ht : 1 < t) : (0 : ℝ) ≤ t⁻¹ := le_of_lt (inv_pos.mpr (tpos ht))

private theorem qlt (ht : 1 < t) : t⁻¹ < 1 := by
  have h0 : (0 : ℝ) < t := tpos ht
  rw [← one_div, div_lt_one h0]
  linarith

private theorem qpow_nonneg (ht : 1 < t) (k : ℕ) : (0 : ℝ) ≤ (t⁻¹) ^ k := pow_nonneg (qnn ht) k

private theorem qpow_le_one (ht : 1 < t) (k : ℕ) : (t⁻¹) ^ k ≤ 1 :=
  pow_le_one₀ (qnn ht) (qlt ht).le

private theorem one_sub_q_pos (ht : 1 < t) : (0 : ℝ) < 1 - t⁻¹ := by
  have := qlt ht; linarith

/-- `latVal` is `legG` at the lattice point — definitionally, but `rw` needs it as an
equation. -/
theorem latVal_def (t : ℝ) (n k : ℕ) :
    latVal t n k = legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹) := rfl

end Elementary

/-! ### The `n`-uniform bound `L_n ≤ (1 − q)⁻¹`

`QHarm/Orthogonality.lean` evaluates the squared norm exactly,
`h_n = ∑_k q^k P_n(q^k)² = t^{n+1}/(t^{2n+1} − 1)`. Bounding it by `(1 − q)⁻¹ = t/(t−1)` and
feeding that into `QHarm/CoefBound.lean`'s Cauchy–Schwarz gives `L_n ≤ (1 − q)⁻¹` uniformly
in `n`. The truth is `≈ t^{-n/2}`, so this is `t^{n/2}` of slack — the campaign is nowhere
near tight here (the internal build notes, "Verified numerics"). -/

private theorem sqnorm_value {t : ℝ} (ht : 1 < t) (n : ℕ) :
    ∑' k : ℕ, (t⁻¹) ^ k * (latVal t n k) ^ 2 = t ^ (n + 1) / (t ^ (2 * n + 1) - 1) := by
  simpa only [latVal_def] using norm_sq_value ht n

private theorem sqnorm_le {t : ℝ} (ht : 1 < t) (n : ℕ) :
    ∑' k : ℕ, (t⁻¹) ^ k * (latVal t n k) ^ 2 ≤ (1 - t⁻¹)⁻¹ := by
  have ht0 : (0 : ℝ) < t := tpos ht
  have ht1 : (0 : ℝ) < t - 1 := by linarith
  have hD : (0 : ℝ) < t ^ (2 * n + 1) - 1 := by
    have h : (1 : ℝ) < t ^ (2 * n + 1) := one_lt_pow₀ ht (by omega)
    linarith
  have hq : (1 - t⁻¹)⁻¹ = t / (t - 1) := by
    rw [show (1 : ℝ) - t⁻¹ = (t - 1) / t from by field_simp, inv_div]
  have hA : (t : ℝ) ^ (n + 1) * t = t ^ (n + 1 + 1) := (pow_succ t (n + 1)).symm
  have hB : (t : ℝ) ^ (2 * n + 1) * t = t ^ (2 * n + 1 + 1) := (pow_succ t (2 * n + 1)).symm
  have hC : (t : ℝ) ^ (n + 1 + 1) ≤ t ^ (2 * n + 1 + 1) := pow_le_pow_right₀ ht.le (by omega)
  have hE : (t : ℝ) ≤ t ^ (n + 1) := by
    have h := pow_le_pow_right₀ ht.le (show 1 ≤ n + 1 by omega)
    rwa [pow_one] at h
  rw [sqnorm_value ht n, hq, div_le_div_iff₀ hD ht1]
  have e1 : (t : ℝ) ^ (n + 1) * (t - 1) = t ^ (n + 1 + 1) - t ^ (n + 1) := by
    rw [← hA]; ring
  have e2 : (t : ℝ) * (t ^ (2 * n + 1) - 1) = t ^ (2 * n + 1 + 1) - t := by
    rw [← hB]; ring
  rw [e1, e2]
  linarith

/-- **The `L`-bound.** `∑_k q^k |P_n(q^k)| ≤ (1 − q)⁻¹`, uniformly in `n`. -/
theorem L_le {t : ℝ} (ht : 1 < t) (n : ℕ) :
    ∑' k : ℕ, (t⁻¹) ^ k * |latVal t n k| ≤ (1 - t⁻¹)⁻¹ := by
  have hpos : (0 : ℝ) < (1 - t⁻¹)⁻¹ := inv_pos.mpr (one_sub_q_pos ht)
  have h := sum_abs_latVal_le ht n (sqnorm_le ht n)
  rwa [Real.mul_self_sqrt hpos.le] at h

/-! ### Summability

One workhorse (`summable_master'`: a bounded numerator against the geometric factor `q^k`)
plus the `k`-uniform coefficient bound from `QHarm/CoefBound.lean`. -/

private theorem summable_master' {t : ℝ} (ht : 1 < t) {g : ℕ → ℝ} {M : ℝ}
    (hg : ∀ k, |g k| ≤ M) : Summable (fun k : ℕ => (t⁻¹) ^ k * g k) := by
  have hq0 : (0 : ℝ) ≤ t⁻¹ := qnn ht
  have hq1 : t⁻¹ < 1 := qlt ht
  have hM : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hg 0)
  refine Summable.of_norm_bounded
    (Summable.mul_left M (summable_geometric_of_lt_one hq0 hq1)) ?_
  intro k
  have hk0 : (0 : ℝ) ≤ (t⁻¹) ^ k := pow_nonneg hq0 k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0]
  calc (t⁻¹) ^ k * |g k| ≤ (t⁻¹) ^ k * M := mul_le_mul_of_nonneg_left (hg k) hk0
    _ = M * (t⁻¹) ^ k := by ring

/-- The `k`-uniform bound on the lattice values, from `QHarm/CoefBound.lean`. -/
private noncomputable def latB (t : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * gaussConst t ^ 2 * t ^ (n.choose 2)

private theorem latB_nonneg {t : ℝ} (ht : 1 < t) (n : ℕ) : 0 ≤ latB t n := by
  unfold latB
  refine mul_nonneg (mul_nonneg ?_ (sq_nonneg _)) (pow_pos (tpos ht) _).le
  positivity

private theorem abs_latVal_le' {t : ℝ} (ht : 1 < t) (n k : ℕ) : |latVal t n k| ≤ latB t n :=
  abs_latVal_le ht n k

private theorem abs_qpow_mul_latVal_le {t : ℝ} (ht : 1 < t) (n k m : ℕ) :
    |((t⁻¹) ^ k) ^ m * latVal t n k| ≤ latB t n := by
  have h1 : |((t⁻¹) ^ k) ^ m| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg (qpow_nonneg ht k) m)]
    exact pow_le_one₀ (qpow_nonneg ht k) (qpow_le_one ht k)
  calc |((t⁻¹) ^ k) ^ m * latVal t n k| = |((t⁻¹) ^ k) ^ m| * |latVal t n k| := abs_mul _ _
    _ ≤ 1 * latB t n := mul_le_mul h1 (abs_latVal_le' ht n k) (abs_nonneg _) zero_le_one
    _ = latB t n := one_mul _

/-- `∑_k (q^k)^{m+1} P_n(q^k)` converges: geometric times a bounded factor. -/
private theorem summable_powLat {t : ℝ} (ht : 1 < t) (n m : ℕ) :
    Summable (fun k : ℕ => ((t⁻¹) ^ k) ^ (m + 1) * latVal t n k) := by
  have h := summable_master' ht (g := fun k : ℕ => ((t⁻¹) ^ k) ^ m * latVal t n k)
    (M := latB t n) (fun k => abs_qpow_mul_latVal_le ht n k m)
  refine h.congr (fun k => ?_)
  rw [← mul_assoc, ← pow_succ']

private theorem inv_den_le {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    ((t : ℝ) ^ n - (t⁻¹) ^ k)⁻¹ ≤ ((t : ℝ) ^ n - 1)⁻¹ := by
  have h1 : (1 : ℝ) < t ^ n := one_lt_pow₀ ht (by omega)
  have hpos : (0 : ℝ) < t ^ n - 1 := by linarith
  have hle : (t : ℝ) ^ n - 1 ≤ t ^ n - (t⁻¹) ^ k := by linarith [qpow_le_one ht k]
  have h := one_div_le_one_div_of_le hpos hle
  rwa [one_div, one_div] at h

/-- The summand of the sum-of-squares form is summable. -/
theorem summable_sq {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun k : ℕ => (t⁻¹) ^ k * (latVal t n k) ^ 2 / ((t : ℝ) ^ n - (t⁻¹) ^ k)) := by
  have h1 : (1 : ℝ) < t ^ n := one_lt_pow₀ ht (by omega)
  have hden : (0 : ℝ) < (t : ℝ) ^ n - 1 := by linarith
  have hbd : ∀ k : ℕ, |(latVal t n k) ^ 2 / ((t : ℝ) ^ n - (t⁻¹) ^ k)|
      ≤ latB t n ^ 2 * ((t : ℝ) ^ n - 1)⁻¹ := by
    intro k
    have hD : (0 : ℝ) < (t : ℝ) ^ n - (t⁻¹) ^ k := pade_den_pos ht hn k
    have hsq : (latVal t n k) ^ 2 ≤ latB t n ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_latVal_le' ht n k) 2
    rw [div_eq_mul_inv, abs_mul, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (inv_nonneg.mpr hD.le)]
    exact mul_le_mul hsq (inv_den_le ht hn k) (inv_nonneg.mpr hD.le)
      (pow_nonneg (latB_nonneg ht n) 2)
  have h := summable_master' ht hbd
  exact h.congr (fun k => (mul_div_assoc _ _ _).symm)

/-- The tail summand of the truncated geometric expansion is summable. -/
private theorem summable_tail {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun k : ℕ =>
      ((t⁻¹) ^ k) ^ (n + 1) * latVal t n k / ((t : ℝ) ^ n - (t⁻¹) ^ k)) := by
  have h1 : (1 : ℝ) < t ^ n := one_lt_pow₀ ht (by omega)
  have hden : (0 : ℝ) < (t : ℝ) ^ n - 1 := by linarith
  have hbd : ∀ k : ℕ, |((t⁻¹) ^ k) ^ n * latVal t n k / ((t : ℝ) ^ n - (t⁻¹) ^ k)|
      ≤ latB t n * ((t : ℝ) ^ n - 1)⁻¹ := by
    intro k
    have hD : (0 : ℝ) < (t : ℝ) ^ n - (t⁻¹) ^ k := pade_den_pos ht hn k
    rw [div_eq_mul_inv, abs_mul, abs_of_nonneg (inv_nonneg.mpr hD.le)]
    exact mul_le_mul (abs_qpow_mul_latVal_le ht n k n) (inv_den_le ht hn k)
      (inv_nonneg.mpr hD.le) (latB_nonneg ht n)
  have h := summable_master' ht hbd
  refine h.congr (fun k => ?_)
  rw [mul_div_assoc', ← mul_assoc, ← pow_succ']

/-! ### Van Assche (34) — the sum-of-squares form -/

/-- `P_n(t^n) − P_n(q^k) = ∑_j γ_{n,j} ((t^n)^j − (q^k)^j)`, the add-and-subtract in the
`legGamma` normalisation. (`QHarm/Pade.lean` proves this too, but privately.) -/
private theorem legVal_sub_latVal' {t : ℝ} (ht : 1 < t) (n k : ℕ) :
    legVal t n - latVal t n k
      = ∑ j ∈ Finset.range (n + 1), legGamma t n j * (((t : ℝ) ^ n) ^ j - ((t⁻¹) ^ k) ^ j) := by
  have ht0 : (0 : ℝ) < t := tpos ht
  have hz : ((t : ℝ) ^ n) ≠ 0 := ne_of_gt (pow_pos ht0 n)
  rw [legVal_eq]
  simp only [latVal, legG]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hzj : (((t : ℝ) ^ n) ^ j) ≠ 0 := pow_ne_zero _ hz
  have h1 : legGamma t n j * (((t : ℝ) ^ n) ^ j) = legCoef t n j := by
    rw [legGamma, mul_assoc, inv_mul_cancel₀ hzj, mul_one]
  have h2 : legGamma t n j * (((t⁻¹) ^ k) ^ j)
      = legCoef t n j * ((t⁻¹) ^ k * ((t : ℝ) ^ n)⁻¹) ^ j := by
    rw [legGamma, mul_pow, inv_pow]
    ring
  rw [mul_sub, h1, h2]

/-- `(P_n(t^n) − P_n(x))/(t^n − x)` is a polynomial of degree `< n` in `x`, written out at
`x = q^k`. Every exponent `j − i` occurring is between `1` and `n`. -/
private theorem cross_term_eq {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (t⁻¹) ^ k * (legVal t n - latVal t n k) / ((t : ℝ) ^ n - (t⁻¹) ^ k)
      = ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range j,
          legGamma t n j * ((t : ℝ) ^ n) ^ i * ((t⁻¹) ^ k) ^ (j - i) := by
  have hD : (0 : ℝ) < (t : ℝ) ^ n - (t⁻¹) ^ k := pade_den_pos ht hn k
  rw [div_eq_iff (ne_of_gt hD), legVal_sub_latVal' ht n k, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hfac : (∑ i ∈ Finset.range j,
      legGamma t n j * ((t : ℝ) ^ n) ^ i * ((t⁻¹) ^ k) ^ (j - i))
      = legGamma t n j * (t⁻¹) ^ k
          * ∑ i ∈ Finset.range j, (((t : ℝ) ^ n) ^ i * ((t⁻¹) ^ k) ^ (j - 1 - i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hij : i < j := Finset.mem_range.mp hi
    have hpow : ((t⁻¹) ^ k) ^ (j - i) = (t⁻¹) ^ k * ((t⁻¹) ^ k) ^ (j - 1 - i) := by
      rw [show j - i = (j - 1 - i) + 1 from by omega, pow_succ]
      ring
    rw [hpow]
    ring
  rw [hfac, mul_assoc (legGamma t n j * (t⁻¹) ^ k), geom_sum₂_mul]
  ring

private theorem summable_cross {t : ℝ} (ht : 1 < t) (n : ℕ) :
    Summable (fun k : ℕ => ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range j,
      legGamma t n j * ((t : ℝ) ^ n) ^ i * (((t⁻¹) ^ k) ^ (j - i) * latVal t n k)) := by
  refine summable_sum (fun j _ => summable_sum (fun i hi => ?_))
  have hij : i < j := Finset.mem_range.mp hi
  rw [show j - i = (j - 1 - i) + 1 from by omega]
  exact (summable_powLat ht n (j - 1 - i)).mul_left _

/-- The cross term dies: every monomial in it has degree `< n`, and `orth_tsum` kills those
one at a time. -/
private theorem tsum_cross_zero {t : ℝ} (ht : 1 < t) {n : ℕ} (_hn : 1 ≤ n) :
    (∑' k : ℕ, ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range j,
      legGamma t n j * ((t : ℝ) ^ n) ^ i * (((t⁻¹) ^ k) ^ (j - i) * latVal t n k)) = 0 := by
  have hin : ∀ j ∈ Finset.range (n + 1), ∀ i ∈ Finset.range j, Summable (fun k : ℕ =>
      legGamma t n j * ((t : ℝ) ^ n) ^ i * (((t⁻¹) ^ k) ^ (j - i) * latVal t n k)) := by
    intro j _ i hi
    have hij : i < j := Finset.mem_range.mp hi
    rw [show j - i = (j - 1 - i) + 1 from by omega]
    exact (summable_powLat ht n (j - 1 - i)).mul_left _
  have houter : ∀ j ∈ Finset.range (n + 1), Summable (fun k : ℕ =>
      ∑ i ∈ Finset.range j,
        legGamma t n j * ((t : ℝ) ^ n) ^ i * (((t⁻¹) ^ k) ^ (j - i) * latVal t n k)) :=
    fun j hj => summable_sum (fun i hi => hin j hj i hi)
  rw [Summable.tsum_finsetSum houter]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Summable.tsum_finsetSum (fun i hi => hin j hj i hi)]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  have hij : i < j := Finset.mem_range.mp hi
  rw [show j - i = (j - 1 - i) + 1 from by omega, tsum_mul_left]
  have h := orth_tsum ht (n := n) (m := j - 1 - i) (by omega)
  rw [show (∑' k : ℕ, ((t⁻¹) ^ k) ^ (j - 1 - i + 1) * latVal t n k) = 0 from h, mul_zero]

/-- **Van Assche (34).** -/
theorem sumsq {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) :
    legVal t n * rem t n
      = ∑' k : ℕ, (t⁻¹) ^ k * (latVal t n k) ^ 2 / ((t : ℝ) ^ n - (t⁻¹) ^ k) := by
  have hA := summable_sq ht hn
  have hB := summable_cross ht n
  have hpt : ∀ k : ℕ,
      legVal t n * ((t⁻¹) ^ k * latVal t n k / ((t : ℝ) ^ n - (t⁻¹) ^ k))
        = (t⁻¹) ^ k * (latVal t n k) ^ 2 / ((t : ℝ) ^ n - (t⁻¹) ^ k)
          + ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range j,
              legGamma t n j * ((t : ℝ) ^ n) ^ i * (((t⁻¹) ^ k) ^ (j - i) * latVal t n k) := by
    intro k
    have hD : ((t : ℝ) ^ n - (t⁻¹) ^ k) ≠ 0 := ne_of_gt (pade_den_pos ht hn k)
    have hcross := cross_term_eq ht hn k
    have h2 : (∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range j,
          legGamma t n j * ((t : ℝ) ^ n) ^ i * ((t⁻¹) ^ k) ^ (j - i)) * latVal t n k
        = ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range j,
            legGamma t n j * ((t : ℝ) ^ n) ^ i * (((t⁻¹) ^ k) ^ (j - i) * latVal t n k) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [← h2, ← hcross]
    field_simp
    ring
  simp only [rem]
  rw [← tsum_mul_left, tsum_congr hpt, Summable.tsum_add hA hB, tsum_cross_zero ht hn,
    add_zero]

/-! ### Strict positivity

Every term is `≥ 0`, so it is enough to exhibit one `k` with `P_n(q^k) ≠ 0`. That comes free
from `Orthogonality.norm_sq_value`: if every lattice value vanished then the squared norm
would be `0`, but it equals `t^{n+1}/(t^{2n+1} − 1) > 0`. -/

private theorem exists_latVal_ne_zero {t : ℝ} (ht : 1 < t) (n : ℕ) :
    ∃ k : ℕ, latVal t n k ≠ 0 := by
  by_contra hcon
  have ht0 : (0 : ℝ) < t := tpos ht
  have hval := sqnorm_value ht n
  have hz : ∀ k : ℕ, (t⁻¹) ^ k * (latVal t n k) ^ 2 = 0 := by
    intro k
    have hk : latVal t n k = 0 := by
      by_contra hk'
      exact hcon ⟨k, hk'⟩
    rw [hk]; ring
  rw [tsum_congr hz, tsum_zero] at hval
  have hD : (0 : ℝ) < t ^ (2 * n + 1) - 1 := by
    have h : (1 : ℝ) < t ^ (2 * n + 1) := one_lt_pow₀ ht (by omega)
    linarith
  have hpos : (0 : ℝ) < t ^ (n + 1) / (t ^ (2 * n + 1) - 1) := div_pos (pow_pos ht0 _) hD
  rw [← hval] at hpos
  exact lt_irrefl 0 hpos

theorem sumsq_pos {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) :
    0 < ∑' k : ℕ, (t⁻¹) ^ k * (latVal t n k) ^ 2 / ((t : ℝ) ^ n - (t⁻¹) ^ k) := by
  obtain ⟨k0, hk0⟩ := exists_latVal_ne_zero ht n
  refine (summable_sq ht hn).tsum_pos (fun k => ?_) k0 ?_
  · exact div_nonneg (mul_nonneg (qpow_nonneg ht k) (sq_nonneg _)) (pade_den_pos ht hn k).le
  · refine div_pos (mul_pos (pow_pos (inv_pos.mpr (tpos ht)) k0) ?_) (pade_den_pos ht hn k0)
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hk0))

/-! ### The quantitative estimate -/

/-- The truncated geometric expansion, exactly: a finite sum of `n` monomials plus a
remainder that already carries the full `t^{-n²}`. No double series is ever formed. -/
private theorem split_term {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (t⁻¹) ^ k * latVal t n k / ((t : ℝ) ^ n - (t⁻¹) ^ k)
      = (∑ r ∈ Finset.range n,
          (((t : ℝ) ^ n)⁻¹) ^ (r + 1) * (((t⁻¹) ^ k) ^ (r + 1) * latVal t n k))
        + ((t : ℝ) ^ (n * n))⁻¹ *
            (((t⁻¹) ^ k) ^ (n + 1) * latVal t n k / ((t : ℝ) ^ n - (t⁻¹) ^ k)) := by
  have ht0 : (0 : ℝ) < t := tpos ht
  have hzp : (0 : ℝ) < (t : ℝ) ^ n := pow_pos ht0 n
  have hDp : (0 : ℝ) < (t : ℝ) ^ n - (t⁻¹) ^ k := pade_den_pos ht hn k
  rw [pow_mul]
  set u : ℝ := (t⁻¹) ^ k
  set z : ℝ := (t : ℝ) ^ n
  set P : ℝ := latVal t n k
  clear_value u z P
  have hz : z ≠ 0 := ne_of_gt hzp
  have hzn : z ^ n ≠ 0 := pow_ne_zero _ hz
  have hD : z - u ≠ 0 := ne_of_gt hDp
  have hsum : (∑ r ∈ Finset.range n, (z⁻¹) ^ (r + 1) * (u ^ (r + 1) * P))
      = (z ^ n)⁻¹ * (u * P * ∑ i ∈ Finset.range n, u ^ i * z ^ (n - 1 - i)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    have hr' : r < n := Finset.mem_range.mp hr
    have he : z ^ (n - 1 - r) * z ^ (r + 1) = z ^ n := by
      rw [← pow_add]; congr 1; omega
    have hzr : (z⁻¹) ^ (r + 1) = z ^ (n - 1 - r) * (z ^ n)⁻¹ := by
      rw [inv_pow, ← he, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero (n - 1 - r) hz), one_mul]
    rw [hzr]
    ring
  have hg2 : (∑ i ∈ Finset.range n, u ^ i * z ^ (n - 1 - i)) * (u - z) = u ^ n - z ^ n :=
    geom_sum₂_mul u z n
  have h0 : u * P * z ^ n
      = u * P * (∑ i ∈ Finset.range n, u ^ i * z ^ (n - 1 - i)) * (z - u) + u ^ (n + 1) * P := by
    linear_combination (u * P) * hg2
  have hkey : u * P
      = (z ^ n)⁻¹ * (u * P * ∑ i ∈ Finset.range n, u ^ i * z ^ (n - 1 - i)) * (z - u)
        + (z ^ n)⁻¹ * (u ^ (n + 1) * P) := by
    field_simp
    linear_combination h0
  rw [hsum]
  conv_lhs => rw [hkey]
  rw [add_div, mul_div_cancel_right₀ _ hD, mul_div_assoc]

/-- Orthogonality annihilates the `n` truncated terms, so `R_n` is exactly `t^{-n²}` times
the tail. -/
private theorem rem_eq_tail {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) :
    rem t n = ((t : ℝ) ^ (n * n))⁻¹ *
      ∑' k : ℕ, ((t⁻¹) ^ k) ^ (n + 1) * latVal t n k / ((t : ℝ) ^ n - (t⁻¹) ^ k) := by
  have hS1 : Summable (fun k : ℕ => ∑ r ∈ Finset.range n,
      (((t : ℝ) ^ n)⁻¹) ^ (r + 1) * (((t⁻¹) ^ k) ^ (r + 1) * latVal t n k)) :=
    summable_sum (fun r _ => (summable_powLat ht n r).mul_left _)
  have hS2 : Summable (fun k : ℕ => ((t : ℝ) ^ (n * n))⁻¹ *
      (((t⁻¹) ^ k) ^ (n + 1) * latVal t n k / ((t : ℝ) ^ n - (t⁻¹) ^ k))) :=
    (summable_tail ht hn).mul_left _
  have hzero : (∑' k : ℕ, ∑ r ∈ Finset.range n,
      (((t : ℝ) ^ n)⁻¹) ^ (r + 1) * (((t⁻¹) ^ k) ^ (r + 1) * latVal t n k)) = 0 := by
    rw [Summable.tsum_finsetSum (fun r _ => (summable_powLat ht n r).mul_left _)]
    refine Finset.sum_eq_zero (fun r hr => ?_)
    rw [tsum_mul_left]
    have h := orth_tsum ht (n := n) (m := r) (Finset.mem_range.mp hr)
    rw [show (∑' k : ℕ, ((t⁻¹) ^ k) ^ (r + 1) * latVal t n k) = 0 from h, mul_zero]
  simp only [rem]
  rw [tsum_congr (split_term ht hn), Summable.tsum_add hS1 hS2, hzero, zero_add, tsum_mul_left]

private theorem abs_rem_le {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) :
    |rem t n| ≤ ((t : ℝ) ^ (n * n))⁻¹ *
      (((t : ℝ) ^ n - 1)⁻¹ * ∑' k : ℕ, (t⁻¹) ^ k * |latVal t n k|) := by
  have ht0 : (0 : ℝ) < t := tpos ht
  have hzinv : (0 : ℝ) ≤ ((t : ℝ) ^ (n * n))⁻¹ := (inv_pos.mpr (pow_pos ht0 _)).le
  have hgabs : Summable
      (fun k : ℕ => |((t⁻¹) ^ k) ^ (n + 1) * latVal t n k / ((t : ℝ) ^ n - (t⁻¹) ^ k)|) :=
    (summable_tail ht hn).abs
  have hL := summable_weight_abs_latVal ht n
  have hbd : ∀ k : ℕ, |((t⁻¹) ^ k) ^ (n + 1) * latVal t n k / ((t : ℝ) ^ n - (t⁻¹) ^ k)|
      ≤ ((t : ℝ) ^ n - 1)⁻¹ * ((t⁻¹) ^ k * |latVal t n k|) := by
    intro k
    have hD : (0 : ℝ) < (t : ℝ) ^ n - (t⁻¹) ^ k := pade_den_pos ht hn k
    have h1 : |((t⁻¹) ^ k) ^ (n + 1) * latVal t n k / ((t : ℝ) ^ n - (t⁻¹) ^ k)|
        = ((t⁻¹) ^ k) ^ (n + 1) * |latVal t n k| * ((t : ℝ) ^ n - (t⁻¹) ^ k)⁻¹ := by
      rw [div_eq_mul_inv, abs_mul, abs_mul,
        abs_of_nonneg (pow_nonneg (qpow_nonneg ht k) (n + 1)),
        abs_of_nonneg (inv_nonneg.mpr hD.le)]
    have h2 : ((t⁻¹) ^ k) ^ (n + 1) ≤ (t⁻¹) ^ k :=
      pow_le_of_le_one (qpow_nonneg ht k) (qpow_le_one ht k) (Nat.succ_ne_zero n)
    rw [h1]
    calc ((t⁻¹) ^ k) ^ (n + 1) * |latVal t n k| * ((t : ℝ) ^ n - (t⁻¹) ^ k)⁻¹
        ≤ (t⁻¹) ^ k * |latVal t n k| * ((t : ℝ) ^ n - 1)⁻¹ := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
            (inv_den_le ht hn k) (inv_nonneg.mpr hD.le) ?_
          exact mul_nonneg (qpow_nonneg ht k) (abs_nonneg _)
      _ = ((t : ℝ) ^ n - 1)⁻¹ * ((t⁻¹) ^ k * |latVal t n k|) := by ring
  rw [rem_eq_tail ht hn, abs_mul, abs_of_nonneg hzinv]
  refine mul_le_mul_of_nonneg_left ?_ hzinv
  calc |∑' k : ℕ, ((t⁻¹) ^ k) ^ (n + 1) * latVal t n k / ((t : ℝ) ^ n - (t⁻¹) ^ k)|
      ≤ ∑' k : ℕ, |((t⁻¹) ^ k) ^ (n + 1) * latVal t n k / ((t : ℝ) ^ n - (t⁻¹) ^ k)| := by
        have h := norm_tsum_le_tsum_norm
          (f := fun k : ℕ =>
            ((t⁻¹) ^ k) ^ (n + 1) * latVal t n k / ((t : ℝ) ^ n - (t⁻¹) ^ k))
          (by simpa only [Real.norm_eq_abs] using hgabs)
        simpa only [Real.norm_eq_abs] using h
    _ ≤ ∑' k : ℕ, ((t : ℝ) ^ n - 1)⁻¹ * ((t⁻¹) ^ k * |latVal t n k|) :=
        Summable.tsum_le_tsum hbd hgabs (hL.mul_left _)
    _ = ((t : ℝ) ^ n - 1)⁻¹ * ∑' k : ℕ, (t⁻¹) ^ k * |latVal t n k| := tsum_mul_left

/-! ### The clearing factor -/

private theorem Mexp_add_gaussExp (n : ℕ) : Mexp n + Clearing.gaussExp n = n * n := by
  have h1 : 2 * Mexp n + n = n * n := two_mul_Mexp_add n
  have h2 : 2 * Clearing.gaussExp n = n * (n + 1) := Clearing.two_mul_gaussExp n
  have h3 : n * (n + 1) = n * n + n := by ring
  omega

theorem clrF_pos {t : ℝ} (ht : 1 < t) (n : ℕ) : 0 < clrF t n :=
  mul_pos (pow_pos (tpos ht) _) (Clearing.Dr_pos ht n)

/-- `clr_n = t^{M_n} D_n ≤ t^{n²}` — the exponents `n(n−1)/2` and `n(n+1)/2` add to `n²`
exactly. -/
theorem clrF_le {t : ℝ} (ht : 1 < t) (n : ℕ) : clrF t n ≤ t ^ (n * n) := by
  have hD : Dr t n ≤ t ^ Clearing.gaussExp n := Clearing.Dr_le_gaussExp ht n
  have hM : (0 : ℝ) < t ^ Mexp n := pow_pos (tpos ht) _
  calc clrF t n = t ^ Mexp n * Dr t n := rfl
    _ ≤ t ^ Mexp n * t ^ Clearing.gaussExp n := mul_le_mul_of_nonneg_left hD hM.le
    _ = t ^ (Mexp n + Clearing.gaussExp n) := (pow_add t _ _).symm
    _ = t ^ (n * n) := by rw [Mexp_add_gaussExp]

/-- The whole balance sheet in one line: `|clr_n R_n| ≤ (1 − q)⁻¹ (t^n − 1)⁻¹`. The `t^{n²}`
of the clearing cancels the `t^{-n²}` of the truncated expansion exactly, and what survives
is the geometric factor `(t^n − 1)⁻¹`, which is what goes to zero. -/
private theorem main_bound {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) :
    |clrF t n * rem t n| ≤ (1 - t⁻¹)⁻¹ * ((t : ℝ) ^ n - 1)⁻¹ := by
  have ht0 : (0 : ℝ) < t := tpos ht
  have hz : (0 : ℝ) < (t : ℝ) ^ (n * n) := pow_pos ht0 _
  have h1 : (1 : ℝ) < t ^ n := one_lt_pow₀ ht (by omega)
  have hden : (0 : ℝ) < (t : ℝ) ^ n - 1 := by linarith
  have hdeninv : (0 : ℝ) ≤ ((t : ℝ) ^ n - 1)⁻¹ := (inv_pos.mpr hden).le
  rw [abs_mul, abs_of_pos (clrF_pos ht n)]
  calc clrF t n * |rem t n|
      ≤ (t : ℝ) ^ (n * n) * |rem t n| :=
        mul_le_mul_of_nonneg_right (clrF_le ht n) (abs_nonneg _)
    _ ≤ (t : ℝ) ^ (n * n) * (((t : ℝ) ^ (n * n))⁻¹ *
          (((t : ℝ) ^ n - 1)⁻¹ * ∑' k : ℕ, (t⁻¹) ^ k * |latVal t n k|)) :=
        mul_le_mul_of_nonneg_left (abs_rem_le ht hn) hz.le
    _ = ((t : ℝ) ^ n - 1)⁻¹ * ∑' k : ℕ, (t⁻¹) ^ k * |latVal t n k| := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hz), one_mul]
    _ ≤ ((t : ℝ) ^ n - 1)⁻¹ * (1 - t⁻¹)⁻¹ := mul_le_mul_of_nonneg_left (L_le ht n) hdeninv
    _ = (1 - t⁻¹)⁻¹ * ((t : ℝ) ^ n - 1)⁻¹ := by ring

/-- **The quantitative estimate.** Stated with the local `clrF`; `clr = clrF` is `rfl`. -/
theorem clr_mul_rem_tendsto_zero {t : ℝ} (ht : 1 < t) :
    Tendsto (fun n : ℕ => |clrF t n * rem t n|) atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ => t ^ n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt ht
  have hsub : Tendsto (fun n : ℕ => t ^ n - 1) atTop atTop := by
    simpa only [← sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hpow
  have hinv : Tendsto (fun n : ℕ => ((t : ℝ) ^ n - 1)⁻¹) atTop (nhds 0) :=
    hsub.inv_tendsto_atTop
  have hg : Tendsto (fun n : ℕ => (1 - t⁻¹)⁻¹ * ((t : ℝ) ^ n - 1)⁻¹) atTop (nhds 0) := by
    simpa using hinv.const_mul ((1 - t⁻¹)⁻¹)
  refine squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _) ?_ hg
  filter_upwards [eventually_ge_atTop 1] with n hn using main_bound ht hn

/-! ### Interface check

`QHarm/Main.lean` states its three `QHarm/Forms.lean` frontiers with exactly the signatures
below. These `example`s are the machine check that what is proved above matches them
verbatim, so the integration step is a copy of the statement and nothing else. (`clr` is
`clrF`: the same definition over the same `Mexp`, restated because `Main.lean` cannot be
imported from here.) -/

example {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) :
    legVal t n * rem t n
      = ∑' k : ℕ, (t⁻¹) ^ k * (latVal t n k) ^ 2 / (t ^ n - (t⁻¹) ^ k) := sumsq ht hn

example {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) :
    0 < ∑' k : ℕ, (t⁻¹) ^ k * (latVal t n k) ^ 2 / (t ^ n - (t⁻¹) ^ k) := sumsq_pos ht hn

example {t : ℝ} (ht : 1 < t) :
    Tendsto (fun n : ℕ => |clrF t n * rem t n|) atTop (nhds 0) := clr_mul_rem_tendsto_zero ht

end QHarm

#print axioms QHarm.sumsq
#print axioms QHarm.sumsq_pos
#print axioms QHarm.clr_mul_rem_tendsto_zero
#print axioms QHarm.L_le
#print axioms QHarm.clrF_le
