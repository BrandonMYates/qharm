/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QHarm.Main
import QHarm.RatSetup
import QHarm.RatDecomp
import QHarm.RatGrowth
import QHarm.RatIntegrality

/-!
# QHarm/MainRat.lean — the rational-base assembly

Like `QHarm/Main.lean` this file contains **no mathematics of its
own** beyond one piece of elementary arithmetic (`two_le_of_theta`): it is the composition step
that turns the finished rational-track component files into `master_rat`.

## Consumes

`QHarm/Basic.lean` (`S`, `irrational_of_linear_forms_tendsto`), `QHarm/Pade.lean` (`pade`),
`QHarm/Main.lean` (`rem_ne_zero`), `QHarm/RatSetup.lean` (`Cexp`, `one_lt_ratBase`),
`QHarm/Cyclotomic.lean` (`Dsharp`, `Dsharp_pos`), `QHarm/RatIntegrality.lean` (`ratA_isInt`,
`ratB_isInt`) and `QHarm/RatGrowth.lean` (`ratClr_mul_rem_tendsto_zero`).  Every input this
file once declared as a placeholder is now closed.

## Main results

* `two_le_of_theta` — `2 ≤ P/Q` follows from the threshold hypothesis alone.  This is the reason
  `QHarm/LegendreBounds.lean`'s `2 ≤ t` hypothesis costs nothing: every rational base the theorem
  covers already satisfies it.
* `master_rat_core` — the theorem in `(P, Q)` coordinates.
* `master_rat` — the theorem in the `ℚ` spelling `QHarm/Reduce.lean` consumes.

## What is NOT here

The integrality of the forms (`QHarm/RatIntegrality.lean`), the growth balance
(`QHarm/RatGrowth.lean`), the closed form for `legG t n ((t^r)⁻¹)` (`QHarm/QLagrange.lean`), the
A-form decomposition (`QHarm/RatDecomp.lean`).
-/

namespace QHarm

open Filter

/-! ### Inputs from the component files -/

/-- Closed by `QHarm/RatIntegrality.lean`. -/
theorem fr_ratB_isInt {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ) :
    ∃ b : ℤ, (Q : ℝ) ^ Cexp n * (Dsharp P Q n : ℝ) * legVal ((P : ℝ) / (Q : ℝ)) n = (b : ℝ) :=
  ratB_isInt hQ hPQ n

/-- Closed by `QHarm/RatIntegrality.lean`. -/
theorem fr_ratA_isInt {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ) :
    ∃ a : ℤ, (Q : ℝ) ^ Cexp n * (Dsharp P Q n : ℝ)
        * (legQval ((P : ℝ) / (Q : ℝ)) n
            + legVal ((P : ℝ) / (Q : ℝ)) n * headSum ((P : ℝ) / (Q : ℝ)) n) = (a : ℝ) :=
  ratA_isInt hQ hPQ n

/-- `QHarm/RatGrowth.lean`'s `ratClr` is definitionally `Q^{C_n} · 𝒟_n`. -/
theorem ratClr_eq (P Q : ℤ) (n : ℕ) :
    ratClr P Q n = (Q : ℝ) ^ Cexp n * (Dsharp P Q n : ℝ) := rfl

/-- Closed by `QHarm/RatGrowth.lean`. -/
theorem fr_ratClr_mul_rem_tendsto_zero {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P)
    (ht2 : (2 : ℝ) ≤ (P : ℝ) / (Q : ℝ))
    (hθ : Real.log (Q : ℝ) / Real.log (P : ℝ) < 1 / 2 - 1 / Real.pi ^ 2) :
    Tendsto (fun n : ℕ =>
        (Q : ℝ) ^ Cexp n * (Dsharp P Q n : ℝ) * |rem ((P : ℝ) / (Q : ℝ)) n|)
      atTop (nhds 0) :=
  ratClr_mul_rem_tendsto_zero hQ hPQ ht2 hθ

/-! ### The clearing factor -/

/-- Positivity of `Q^{C_n} · 𝒟_n`. -/
theorem ratClr_pos' {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ) :
    0 < (Q : ℝ) ^ Cexp n * (Dsharp P Q n : ℝ) := by
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hD : (0 : ℝ) < (Dsharp P Q n : ℝ) := by exact_mod_cast Dsharp_pos hQ hPQ n
  exact mul_pos (pow_pos hQR _) hD

/-- The Padé identity in the shape `QHarm/Basic.lean`'s criterion consumes, for an arbitrary
positive clearing factor `c`. -/
theorem form_eq_gen {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) (c : ℝ) :
    c * legVal t n * S t - c * (legQval t n + legVal t n * headSum t n)
      = c * rem t n := by
  have h := pade ht hn
  linear_combination c * h

/-! ### The threshold forces `2 ≤ t`

Every rational base the theorem covers is at least `2`.  If `Q = 1` this is `P ≥ 2`; if `Q ≥ 2`
then `θ < 1/2` gives `Q² < P`, hence `2Q ≤ Q² < P`.  The only transcendental input is
`Real.pi_gt_three`. -/

theorem two_le_of_theta {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P)
    (hθ : Real.log (Q : ℝ) / Real.log (P : ℝ) < 1 / 2 - 1 / Real.pi ^ 2) :
    (2 : ℝ) ≤ (P : ℝ) / (Q : ℝ) := by
  have hQ1 : (1 : ℤ) ≤ Q := hQ
  have hP2 : (2 : ℤ) ≤ P := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hPR2 : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP2
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  -- `1/π² < 1/2`
  have hpi : (2 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
  have hpipos : (0 : ℝ) < Real.pi ^ 2 := by linarith
  have hhalf : 1 / Real.pi ^ 2 < 1 / 2 := by
    rw [div_lt_div_iff₀ hpipos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hinvpos : (0 : ℝ) < 1 / Real.pi ^ 2 := by positivity
  have hθ' : Real.log (Q : ℝ) / Real.log (P : ℝ) < 1 / 2 := by linarith
  rcases eq_or_lt_of_le hQ1 with hQe | hQ2
  · -- `Q = 1`
    have hQ1' : Q = 1 := hQe.symm
    subst hQ1'
    simp only [Int.cast_one, div_one]
    exact hPR2
  · -- `2 ≤ Q`
    have hQ2' : (2 : ℤ) ≤ Q := hQ2
    have hQR2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ2'
    have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos (by linarith)
    have hmul : Real.log (Q : ℝ) < 1 / 2 * Real.log (P : ℝ) := by
      rw [div_lt_iff₀ hlogP] at hθ'
      linarith
    have hsq : Real.log (((Q * Q : ℤ) : ℝ)) < Real.log (P : ℝ) := by
      push_cast
      rw [Real.log_mul (by linarith) (by linarith)]
      linarith
    have hQQ : (Q * Q : ℤ) < P := by
      have hc : (((Q * Q : ℤ)) : ℝ) < (P : ℝ) := by
        by_contra hcon
        rw [not_lt] at hcon
        have hle : Real.log (P : ℝ) ≤ Real.log (((Q * Q : ℤ) : ℝ)) :=
          Real.log_le_log (by linarith) hcon
        linarith
      exact_mod_cast hc
    have h2Q : 2 * Q ≤ Q * Q := by nlinarith
    have : (2 : ℝ) * (Q : ℝ) < (P : ℝ) := by
      have : ((2 * Q : ℤ) : ℝ) < (P : ℝ) := by exact_mod_cast lt_of_le_of_lt h2Q hQQ
      push_cast at this
      linarith
    rw [le_div_iff₀ hQR]
    linarith

/-! ### The assembly -/

/-- **The rational-base master theorem, in `(P, Q)` coordinates.** -/
theorem master_rat_core {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P)
    (hθ : Real.log (Q : ℝ) / Real.log (P : ℝ) < 1 / 2 - 1 / Real.pi ^ 2) :
    Irrational (S ((P : ℝ) / (Q : ℝ))) := by
  have ht1 : (1 : ℝ) < (P : ℝ) / (Q : ℝ) := one_lt_ratBase hQ hPQ
  have ht2 : (2 : ℝ) ≤ (P : ℝ) / (Q : ℝ) := two_le_of_theta hQ hPQ hθ
  choose B hB using fr_ratB_isInt hQ hPQ
  choose A hA using fr_ratA_isInt hQ hPQ
  refine irrational_of_linear_forms_tendsto A B ?_ ?_
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [← hB 0, ← hA 0]
      simp only [legVal_zero, legQval_zero, headSum_zero, mul_zero, mul_one, add_zero,
        sub_zero]
      exact ne_of_gt (mul_pos (ratClr_pos' hQ hPQ 0) (S_pos ht1))
    · rw [← hB n, ← hA n, form_eq_gen ht1 hn]
      exact mul_ne_zero (ne_of_gt (ratClr_pos' hQ hPQ n)) (rem_ne_zero ht1 hn)
  · refine Tendsto.congr' ?_ (fr_ratClr_mul_rem_tendsto_zero hQ hPQ ht2 hθ)
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← hB n, ← hA n, form_eq_gen ht1 hn, abs_mul,
      abs_of_pos (ratClr_pos' hQ hPQ n)]

/-- **The rational-base master theorem.**  For every rational `t > 1` in lowest terms with
`log t.den / log t.num < 1/2 − 1/π²`, the `q`-harmonic series is irrational. -/
theorem master_rat (t : ℚ) (ht : 1 < t)
    (hθ : Real.log (t.den : ℝ) / Real.log (t.num : ℝ) < 1 / 2 - 1 / Real.pi ^ 2) :
    Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)) := by
  have hdenQ : (0 : ℚ) < (t.den : ℚ) := by exact_mod_cast t.pos
  have hnumQ : (t.num : ℚ) = t * (t.den : ℚ) :=
    (div_eq_iff (ne_of_gt hdenQ)).mp (Rat.num_div_den t)
  have hlt : (t.den : ℚ) < (t.num : ℚ) := by
    rw [hnumQ]
    nlinarith
  have hQ : (0 : ℤ) < (t.den : ℤ) := by exact_mod_cast t.pos
  have hPQ : ((t.den : ℤ)) < t.num := by exact_mod_cast hlt
  have hcast : ((t : ℚ) : ℝ) = ((t.num : ℤ) : ℝ) / (((t.den : ℤ)) : ℝ) := by
    rw [Rat.cast_def]
    push_cast
    ring
  show Irrational (S ((t : ℚ) : ℝ))
  rw [hcast]
  refine master_rat_core hQ hPQ ?_
  push_cast
  exact hθ

end QHarm

#print axioms QHarm.two_le_of_theta
#print axioms QHarm.master_rat_core
#print axioms QHarm.master_rat
