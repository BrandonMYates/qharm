/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QHarm.Growth
import QHarm.LegendreBounds

/-!
# `QHarm/RatGrowth.lean` — the rational-base balance

The single quantitative statement the rational track needs from the growth side: with the
rational clearing factor `Q^{C_n}·𝒟_n` (`C_n = degTerm n n = n(3n−1)/2`) the linear forms
tend to `0`, provided `θ = log Q / log P < 1/2 − 1/π²`.

## Consumes

* `QHarm/Cyclotomic.lean` — `Dsharp`, `Dsharp_pos`;
* `QHarm/Growth.lean` — `log_Dsharp_le_eventually`, the one-sided sharp growth
  `log 𝒟_n ≤ ((3/π²)·log P + ε)·n²` eventually, for every `ε > 0`;
* `QHarm/LegendreBounds.lean` — `degTerm`, `degTerm_diag`, `two_mul_degTerm_diag`, and the
  sharp remainder bound `eventually_abs_rem_le`;
* `QHarm/Pade.lean` — `rem` (through `LegendreBounds`).

Every dependency is `sorry`-free, so every statement below is proved outright.

## Main results

* `QHarm.ratClr` — the rational clearing factor `Q^{C_n}·𝒟_n` as a real number.
* `QHarm.ratClr_pos` — it is positive.
* `QHarm.ratBase_log_P_pos` — `0 < log P` (from `Q ≥ 1`, `P > Q`, hence `P ≥ 2`).
* `QHarm.ratClr_le` — `log (Q^{C_n}·𝒟_n) = C_n·log Q + log 𝒟_n`.
* `QHarm.eventually_abs_rem_le_crude` — the deliberately lossy repackaging of
  `LegendreBounds.eventually_abs_rem_le`: eventually `|rem t n| ≤ 8 / t^{C_n}` for `t ≥ 2`.
* `QHarm.ratClr_mul_rem_tendsto_zero` — **the balance**: under
  `2 ≤ P/Q` and `log Q / log P < 1/2 − 1/π²`,
  `Q^{C_n}·𝒟_n·|rem (P/Q) n| → 0`.

## The balance, in one line

Write `L_P = log P > 0`, `L_Q = log Q ≥ 0`, `θ = L_Q/L_P`, `δ = (1/2 − 1/π²) − θ > 0`,
`ε = (3/2)·δ·L_P > 0`.  Crudely `|rem t n| ≤ 8/t^{C_n}` and `t^{C_n} = P^{C_n}/Q^{C_n}`, so

    ratClr · |rem| ≤ 8 · 𝒟_n · Q^{2C_n} / P^{C_n} = 8 · exp(2C_n L_Q + log 𝒟_n − C_n L_P).

With `2C_n = 3n² − n` (`two_mul_degTerm_diag`) and `log 𝒟_n ≤ ((3/π²)L_P + ε)n²` the exponent
is at most `A·n² + B·n` with

    A = (3/π²)L_P + ε + 3L_Q − (3/2)L_P = −(3/2)·δ·L_P < 0,   B = L_P/2 − L_Q,

the `n`-terms cancelling identically.  `exp(A n² + B n) → 0` and `squeeze_zero'` finishes.
`Q = 1` is covered: then `L_Q = 0`, `θ = 0`, `δ = 1/2 − 1/π² > 0`.

The estimate is enormously lossy in `n` (the true remainder is `≈ t^{−3n²/2−3n/2}`), which is
deliberate — the verified numerics in the build notes record that nothing downstream is tight.

## What is NOT here

* **No integrality statement.**  That `Q^{C_n}·𝒟_n·A_n` and `Q^{C_n}·𝒟_n·B_n` are integers is
  `QHarm/RatSetup.lean` and `QHarm/RatIntegrality.lean`.
* **No nonvanishing.**  `B_n S − A_n ≠ 0` comes from the sum-of-squares identity (34) via
  `QHarm/Forms.lean` / `QHarm/LegendreBounds.lean` (`legVal_ne_zero`, `legVal_sign`), not here.
* the growth of `𝒟_n` itself — `QHarm/Growth.lean`;
* the cyclotomic clearing factor and its divisibility — `QHarm/Cyclotomic.lean`;
* the lower bound on `|P_n(t^n)|` and the sharp remainder — `QHarm/LegendreBounds.lean`;
* the assembly into `master_rat` — `QHarm/MainRat.lean`.
-/

namespace QHarm

open Filter

/-! ### A crude repackaging of the sharp remainder bound

`LegendreBounds.eventually_abs_rem_le` delivers
`|rem t n| ≤ (2 t^{n+1}/((t^n−1)(t^{2n+1}−1))) / t^{C_n}`.  For `t ≥ 2` and `n ≥ 1` the leading
factor is at most `8` — in fact at most `8 t^{−2n}`, but the balance has `n²` of slack, so the
constant is thrown away. -/

/-- For `t ≥ 2` and `n ≥ 1`, `2 t^{n+1} / ((t^n − 1)(t^{2n+1} − 1)) ≤ 8`.

Proof: `t^n − 1 ≥ t^n/2` and `t^{2n+1} − 1 ≥ t^{2n+1}/2` (both powers are `≥ 2`), so the
denominator is `≥ t^{3n+1}/4`, and `t^{n+1} ≤ t^{3n+1}`. -/
private theorem rem_factor_le {t : ℝ} (ht : 2 ≤ t) {n : ℕ} (hn : 1 ≤ n) :
    2 * t ^ (n + 1) / ((t ^ n - 1) * (t ^ (2 * n + 1) - 1)) ≤ 8 := by
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have h1 : (2 : ℝ) ≤ t ^ n := by
    calc (2 : ℝ) ≤ t := ht
      _ = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ n := pow_le_pow_right₀ ht1 hn
  have h2 : (2 : ℝ) ≤ t ^ (2 * n + 1) := by
    calc (2 : ℝ) ≤ t := ht
      _ = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ (2 * n + 1) := pow_le_pow_right₀ ht1 (by omega)
  have hd1 : t ^ n / 2 ≤ t ^ n - 1 := by linarith
  have hd2 : t ^ (2 * n + 1) / 2 ≤ t ^ (2 * n + 1) - 1 := by linarith
  have hden : (0 : ℝ) < (t ^ n - 1) * (t ^ (2 * n + 1) - 1) := by
    apply mul_pos <;> linarith
  have hmul : t ^ n / 2 * (t ^ (2 * n + 1) / 2) ≤ (t ^ n - 1) * (t ^ (2 * n + 1) - 1) :=
    mul_le_mul hd1 hd2 (by linarith) (by linarith)
  have hexp : t ^ n * t ^ (2 * n + 1) = t ^ (3 * n + 1) := by
    rw [← pow_add]; congr 1; omega
  have heq : t ^ n / 2 * (t ^ (2 * n + 1) / 2) = t ^ (3 * n + 1) / 4 := by
    rw [← hexp]; ring
  rw [heq] at hmul
  have hle : t ^ (n + 1) ≤ t ^ (3 * n + 1) := pow_le_pow_right₀ ht1 (by omega)
  rw [div_le_iff₀ hden]
  linarith

/-- The lossy remainder bound the rational balance consumes: for `t ≥ 2`, eventually
`|rem t n| ≤ 8 / t^{C_n}` with `C_n = degTerm n n`. -/
theorem eventually_abs_rem_le_crude {t : ℝ} (ht : 2 ≤ t) :
    ∀ᶠ n : ℕ in atTop, |rem t n| ≤ 8 / t ^ degTerm n n := by
  have ht0 : (0 : ℝ) < t := by linarith
  filter_upwards [eventually_abs_rem_le ht, Filter.eventually_ge_atTop 1] with n hn hn1
  have hinv : (0 : ℝ) ≤ (t ^ degTerm n n)⁻¹ := inv_nonneg.mpr (pow_pos ht0 _).le
  calc |rem t n|
      ≤ (2 * t ^ (n + 1) / ((t ^ n - 1) * (t ^ (2 * n + 1) - 1))) / t ^ degTerm n n := hn
    _ = (2 * t ^ (n + 1) / ((t ^ n - 1) * (t ^ (2 * n + 1) - 1))) * (t ^ degTerm n n)⁻¹ :=
        div_eq_mul_inv _ _
    _ ≤ 8 * (t ^ degTerm n n)⁻¹ := mul_le_mul_of_nonneg_right (rem_factor_le ht hn1) hinv
    _ = 8 / t ^ degTerm n n := (div_eq_mul_inv _ _).symm

/-! ### The rational clearing factor -/

/-- The rational-base clearing factor `Q^{C_n} · 𝒟_n`, with `C_n = degTerm n n = n(3n−1)/2`. -/
noncomputable def ratClr (P Q : ℤ) (n : ℕ) : ℝ := (Q : ℝ) ^ degTerm n n * (Dsharp P Q n : ℝ)

theorem ratClr_pos {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ) : 0 < ratClr P Q n := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hD0 : (0 : ℝ) < ((Dsharp P Q n : ℤ) : ℝ) := by exact_mod_cast Dsharp_pos hQ hPQ n
  exact mul_pos (pow_pos hQ0 _) hD0

/-- `P ≥ 2`, hence `log P > 0`.  (`Q ≥ 1` because `Q > 0` in `ℤ`, and `P > Q`.) -/
theorem ratBase_log_P_pos {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) : 0 < Real.log (P : ℝ) := by
  have h2 : (2 : ℤ) ≤ P := by omega
  have h2' : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast h2
  exact Real.log_pos (by linarith)

/-- `log (Q^{C_n}·𝒟_n) = C_n·log Q + log 𝒟_n`.  At `Q = 1` the first summand is `0`. -/
theorem ratClr_le {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ) :
    Real.log (ratClr P Q n) = (degTerm n n : ℝ) * Real.log (Q : ℝ) + Real.log (Dsharp P Q n : ℝ) := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hD0 : (0 : ℝ) < ((Dsharp P Q n : ℤ) : ℝ) := by exact_mod_cast Dsharp_pos hQ hPQ n
  simp only [ratClr]
  rw [Real.log_mul (pow_pos hQ0 _).ne' hD0.ne', Real.log_pow]

/-! ### `exp(A n² + B n) → 0` for `A < 0` -/

private theorem tendsto_exp_quad {A B : ℝ} (hA : A < 0) :
    Tendsto (fun n : ℕ => Real.exp (A * (n : ℝ) ^ 2 + B * (n : ℝ))) atTop (nhds 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => A * (n : ℝ) + B) atTop atBot :=
    tendsto_atBot_add_const_right _ B (hnat.const_mul_atTop_of_neg hA)
  have h2 : Tendsto (fun n : ℕ => (A * (n : ℝ) + B) * (n : ℝ)) atTop atBot :=
    h1.atBot_mul_atTop₀ hnat
  have h3 : (fun n : ℕ => (A * (n : ℝ) + B) * (n : ℝ))
      = fun n : ℕ => A * (n : ℝ) ^ 2 + B * (n : ℝ) := by
    funext n; ring
  rw [h3] at h2
  simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp h2

/-! ### The balance -/

/-- **The balance.**  Under the threshold hypothesis the linear forms tend to 0. -/
theorem ratClr_mul_rem_tendsto_zero {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P)
    (ht2 : (2 : ℝ) ≤ (P : ℝ) / (Q : ℝ))
    (hθ : Real.log (Q : ℝ) / Real.log (P : ℝ) < 1 / 2 - 1 / Real.pi ^ 2) :
    Filter.Tendsto (fun n : ℕ => ratClr P Q n * |rem ((P : ℝ) / (Q : ℝ)) n|)
      Filter.atTop (nhds 0) := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hP2 : (2 : ℤ) ≤ P := by omega
  have hP0 : (0 : ℝ) < (P : ℝ) := by
    have : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP2
    linarith
  have hLP : 0 < Real.log (P : ℝ) := ratBase_log_P_pos hQ hPQ
  -- the margin `δ` and the growth slack `ε`
  obtain ⟨δ, hδdef⟩ :
      ∃ d : ℝ, d = 1 / 2 - 1 / Real.pi ^ 2 - Real.log (Q : ℝ) / Real.log (P : ℝ) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hεpos : (0 : ℝ) < 3 / 2 * δ * Real.log (P : ℝ) :=
    mul_pos (mul_pos (by norm_num) hδ) hLP
  have hA : -(3 / 2) * δ * Real.log (P : ℝ) < 0 := by nlinarith
  have hLQeq : Real.log (Q : ℝ) = (1 / 2 - 1 / Real.pi ^ 2 - δ) * Real.log (P : ℝ) := by
    have h : 1 / 2 - 1 / Real.pi ^ 2 - δ = Real.log (Q : ℝ) / Real.log (P : ℝ) := by
      rw [hδdef]; ring
    rw [h, div_mul_cancel₀ _ hLP.ne']
  -- the eventual upper bound
  have hbound : ∀ᶠ n : ℕ in atTop,
      ratClr P Q n * |rem ((P : ℝ) / (Q : ℝ)) n|
        ≤ 8 * Real.exp ((-(3 / 2) * δ * Real.log (P : ℝ)) * (n : ℝ) ^ 2
            + (Real.log (P : ℝ) / 2 - Real.log (Q : ℝ)) * (n : ℝ)) := by
    filter_upwards [eventually_abs_rem_le_crude ht2,
      log_Dsharp_le_eventually hQ hPQ hεpos] with n hrem hgrow
    have hQC : (0 : ℝ) < (Q : ℝ) ^ degTerm n n := pow_pos hQ0 _
    have hPC : (0 : ℝ) < (P : ℝ) ^ degTerm n n := pow_pos hP0 _
    have hD0 : (0 : ℝ) < ((Dsharp P Q n : ℤ) : ℝ) := by exact_mod_cast Dsharp_pos hQ hPQ n
    have hqc : Real.exp ((degTerm n n : ℝ) * Real.log (Q : ℝ)) = (Q : ℝ) ^ degTerm n n := by
      rw [← Real.log_pow, Real.exp_log hQC]
    have hpc : Real.exp ((degTerm n n : ℝ) * Real.log (P : ℝ)) = (P : ℝ) ^ degTerm n n := by
      rw [← Real.log_pow, Real.exp_log hPC]
    have hexp : (Q : ℝ) ^ degTerm n n * (Q : ℝ) ^ degTerm n n * ((Dsharp P Q n : ℤ) : ℝ)
          / (P : ℝ) ^ degTerm n n
        = Real.exp (2 * (degTerm n n : ℝ) * Real.log (Q : ℝ)
            + Real.log ((Dsharp P Q n : ℤ) : ℝ) - (degTerm n n : ℝ) * Real.log (P : ℝ)) := by
      have e1 : (2 : ℝ) * (degTerm n n : ℝ) * Real.log (Q : ℝ)
          = (degTerm n n : ℝ) * Real.log (Q : ℝ) + (degTerm n n : ℝ) * Real.log (Q : ℝ) := by
        ring
      rw [e1, Real.exp_sub, Real.exp_add, Real.exp_add, hqc, hpc, Real.exp_log hD0]
    -- the `n²`-coefficient is exactly `−(3/2)δ log P`, and the `n`-terms cancel
    have hcast : 2 * (degTerm n n : ℝ) + (n : ℝ) = 3 * ((n : ℝ) * (n : ℝ)) := by
      exact_mod_cast two_mul_degTerm_diag n
    have hcval : (degTerm n n : ℝ) = (3 * (n : ℝ) * (n : ℝ) - (n : ℝ)) / 2 := by linarith
    have hident :
        (-(3 / 2) * δ * Real.log (P : ℝ)) * (n : ℝ) ^ 2
            + (Real.log (P : ℝ) / 2 - Real.log (Q : ℝ)) * (n : ℝ)
            - (2 * (degTerm n n : ℝ) * Real.log (Q : ℝ)
                + Real.log ((Dsharp P Q n : ℤ) : ℝ) - (degTerm n n : ℝ) * Real.log (P : ℝ))
          = (3 / Real.pi ^ 2 * Real.log (P : ℝ) + 3 / 2 * δ * Real.log (P : ℝ)) * (n : ℝ) ^ 2
            - Real.log ((Dsharp P Q n : ℤ) : ℝ) := by
      rw [hcval, hLQeq]; ring
    have hexpbound :
        2 * (degTerm n n : ℝ) * Real.log (Q : ℝ) + Real.log ((Dsharp P Q n : ℤ) : ℝ)
            - (degTerm n n : ℝ) * Real.log (P : ℝ)
          ≤ (-(3 / 2) * δ * Real.log (P : ℝ)) * (n : ℝ) ^ 2
            + (Real.log (P : ℝ) / 2 - Real.log (Q : ℝ)) * (n : ℝ) := by
      nlinarith [hident, hgrow]
    calc ratClr P Q n * |rem ((P : ℝ) / (Q : ℝ)) n|
        ≤ ratClr P Q n * (8 / ((P : ℝ) / (Q : ℝ)) ^ degTerm n n) :=
          mul_le_mul_of_nonneg_left hrem (ratClr_pos hQ hPQ n).le
      _ = 8 * ((Q : ℝ) ^ degTerm n n * (Q : ℝ) ^ degTerm n n * ((Dsharp P Q n : ℤ) : ℝ)
              / (P : ℝ) ^ degTerm n n) := by
          simp only [ratClr]
          rw [div_pow, div_div_eq_mul_div]
          ring
      _ = 8 * Real.exp (2 * (degTerm n n : ℝ) * Real.log (Q : ℝ)
              + Real.log ((Dsharp P Q n : ℤ) : ℝ) - (degTerm n n : ℝ) * Real.log (P : ℝ)) := by
          rw [hexp]
      _ ≤ 8 * Real.exp ((-(3 / 2) * δ * Real.log (P : ℝ)) * (n : ℝ) ^ 2
              + (Real.log (P : ℝ) / 2 - Real.log (Q : ℝ)) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexpbound) (by norm_num)
  refine squeeze_zero' ?_ hbound ?_
  · filter_upwards with n
    exact mul_nonneg (ratClr_pos hQ hPQ n).le (abs_nonneg _)
  · simpa using (tendsto_exp_quad (B := Real.log (P : ℝ) / 2 - Real.log (Q : ℝ)) hA).const_mul 8

end QHarm

#print axioms QHarm.eventually_abs_rem_le_crude
#print axioms QHarm.ratClr_pos
#print axioms QHarm.ratBase_log_P_pos
#print axioms QHarm.ratClr_le
#print axioms QHarm.ratClr_mul_rem_tendsto_zero
