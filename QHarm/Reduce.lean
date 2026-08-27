/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import QHarm.Main
import QHarm.MainRat

/-!
# QHarm/Reduce.lean — the three Challenge statements, reduced to two master theorems

## Consumes

The two master theorems, and nothing else from `QHarm`:

* `QHarm.master_int`  — `QHarm/Main.lean` (integer track, deviation D1)
* `QHarm.master_rat`  — `QHarm/MainRat.lean` (general rational-base track)

Everything else in this file is elementary `Real.log` monotonicity and a `π > 3` bound,
and was built and audited before the rest of the DAG landed.

## Main results

The three advertised statements of the Palomar Challenge file for this entry, with
**term-identical** conclusions:

* `QHarmonicRationalBase.irrational_of_logRatio_lt`
* `QHarmonicRationalBase.irrational_half_odd`
* `QHarmonicRationalBase.irrational_int`

together with the arithmetic that reduces them to the two masters. All of that
arithmetic is fully proved here:

* `QHarm.Reduce.cast_half_odd`      — `(((P : ℚ)/2 : ℚ) : ℝ) = (P : ℝ)/2`
* `QHarm.Reduce.one_lt_half_odd`    — `1 < (P : ℚ)/2` for `7 ≤ P`
* `QHarm.Reduce.num_half_odd`       — `((P : ℚ)/2).num = P` for `P` odd
* `QHarm.Reduce.den_half_odd`       — `((P : ℚ)/2).den = 2` for `P` odd
* `QHarm.Reduce.log_seven_gt`       — `(13/5) * log 2 < log 7`
* `QHarm.Reduce.log_two_div_log_seven_lt` — `log 2 / log 7 < 5/13`
* `QHarm.Reduce.log_two_div_log_lt` — `log 2 / log P < 1/2 − 1/π²` for `7 ≤ P`
* `QHarm.Reduce.logRatio_int_lt`    — the (unused-but-on-record) `θ = 0` threshold check

## What is NOT here

* The masters themselves (`QHarm/Main.lean`).
* Anything about the linear forms, the clearing factor (`QHarm/Clearing.lean`), the
  q-Legendre polynomials, orthogonality, or the growth estimates. This file contains
  no analysis beyond elementary `Real.log` monotonicity and a `π > 3` bound.
* Irrationality measures / `LiouvilleWith`: deliberately not advertised.
-/

namespace QHarm

/-! Both masters are now **proved** and imported above — `master_int` in `QHarm/Main.lean`
(integer track, deviation D1) and `master_rat` in `QHarm/MainRat.lean` (general rational-base
track).  The two placeholders that stood here are closed; this file carries no `sorry`. -/

namespace Reduce

/-! ### Step 1 — the cast bridge

The Challenge spells the half-odd base as the *real* number `(P : ℝ) / 2`, while
`master_rat` is stated for a *rational* `t` coerced into `ℝ`. This lemma is what makes
the two `tsum`s the same term. -/

/-- `(P : ℚ)/2` and `(P : ℝ)/2` name the same real number. -/
theorem cast_half_odd (P : ℕ) : ((((P : ℚ) / 2 : ℚ)) : ℝ) = (P : ℝ) / 2 := by
  push_cast
  ring

/-! ### Step 2 — positivity of the base -/

/-- For `P ≥ 7` the base `P/2` exceeds `1` (indeed it exceeds `7/2`). -/
theorem one_lt_half_odd (P : ℕ) (hP : 7 ≤ P) : 1 < ((P : ℚ) / 2) := by
  have h : (7 : ℚ) ≤ (P : ℚ) := by exact_mod_cast hP
  linarith

/-! ### Step 3 — `P/2` is already in lowest terms

`Rat.num_div_eq_of_coprime` / `Rat.den_div_eq_of_coprime` (Mathlib
`Data/Rat/Lemmas.lean`) are stated for `a b : ℤ` with `0 < b` and
`Nat.Coprime a.natAbs b.natAbs`. -/

/-- `P` odd gives `Nat.Coprime |P| |2|` in the shape the `Rat` API wants. -/
theorem coprime_half_odd (P : ℕ) (hodd : Odd P) :
    Nat.Coprime ((P : ℤ)).natAbs ((2 : ℤ)).natAbs := by
  simpa using Nat.coprime_two_right.mpr hodd

/-- The two spellings of the base, over `ℚ`. -/
theorem rat_half_eq (P : ℕ) : (((P : ℤ) : ℚ)) / (((2 : ℤ) : ℚ)) = (P : ℚ) / 2 := by
  push_cast
  ring

/-- The numerator of `P/2` is `P`, for odd `P`. -/
theorem num_half_odd (P : ℕ) (hodd : Odd P) : ((P : ℚ) / 2).num = (P : ℤ) := by
  have h := Rat.num_div_eq_of_coprime (a := (P : ℤ)) (b := (2 : ℤ)) (by norm_num)
    (coprime_half_odd P hodd)
  rwa [rat_half_eq P] at h

/-- The denominator of `P/2` is `2`, for odd `P`. -/
theorem den_half_odd (P : ℕ) (hodd : Odd P) : ((P : ℚ) / 2).den = 2 := by
  have h := Rat.den_div_eq_of_coprime (a := (P : ℤ)) (b := (2 : ℤ)) (by norm_num)
    (coprime_half_odd P hodd)
  rw [rat_half_eq P] at h
  exact_mod_cast h

/-! ### Step 4 — the numeric threshold

`log 2 / log P < 1/2 − 1/π²` for `P ≥ 7`, via `7^5 = 16807 > 8192 = 2^13` and `π > 3`.
No transcendental estimate beyond `Real.pi_gt_three` is used. -/

/-- `7^5 = 16807 > 8192 = 2^13`, hence `log 7 > (13/5) log 2`. -/
theorem log_seven_gt : (13 / 5 : ℝ) * Real.log 2 < Real.log 7 := by
  have h1 : ((2 : ℝ) ^ (13 : ℕ)) < ((7 : ℝ) ^ (5 : ℕ)) := by norm_num
  have h2 : Real.log ((2 : ℝ) ^ (13 : ℕ)) < Real.log ((7 : ℝ) ^ (5 : ℕ)) :=
    Real.log_lt_log (by norm_num) h1
  rw [Real.log_pow, Real.log_pow] at h2
  push_cast at h2
  linarith

/-- `log 2 / log 7 < 5/13`. -/
theorem log_two_div_log_seven_lt : Real.log 2 / Real.log 7 < 5 / 13 := by
  have h7 : (0 : ℝ) < Real.log 7 := Real.log_pos (by norm_num)
  rw [div_lt_div_iff₀ h7 (by norm_num : (0 : ℝ) < 13)]
  linarith [log_seven_gt]

/-- `π² > 26/3`; the only transcendental input is `Real.pi_gt_three`. -/
theorem pi_sq_gt : (26 / 3 : ℝ) < Real.pi ^ 2 := by
  nlinarith [Real.pi_gt_three, Real.pi_pos]

/-- `5/13 < 1/2 − 1/π²`, equivalently `1/π² < 3/26`. -/
theorem five_div_thirteen_lt : (5 / 13 : ℝ) < 1 / 2 - 1 / Real.pi ^ 2 := by
  have hpos : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have h : 1 / Real.pi ^ 2 < 3 / 26 := by
    rw [div_lt_div_iff₀ hpos (by norm_num : (0 : ℝ) < 26)]
    linarith [pi_sq_gt]
  linarith

/-- **The numeric threshold.** For every natural `P ≥ 7`,
`log 2 / log P < 1/2 − 1/π²`. -/
theorem log_two_div_log_lt {P : ℕ} (hP : 7 ≤ P) :
    Real.log 2 / Real.log (P : ℝ) < 1 / 2 - 1 / Real.pi ^ 2 := by
  have h7 : (0 : ℝ) < Real.log 7 := Real.log_pos (by norm_num)
  have hPR : (7 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hlog : Real.log 7 ≤ Real.log (P : ℝ) := Real.log_le_log (by norm_num) hPR
  have hstep : Real.log 2 / Real.log (P : ℝ) ≤ Real.log 2 / Real.log 7 :=
    div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) h7 hlog
  linarith [log_two_div_log_seven_lt, five_div_thirteen_lt]

set_option linter.unusedVariables false in
/-- The `θ = 0` threshold check for an integer base. `irrational_int` is routed through
`QHarm.master_int` (deviation D1), so this lemma is not consumed by anything below; it
is on record that the rational route would also have applied. (The hypothesis `2 ≤ t`
is kept for signature parity with `master_int`; the estimate in fact holds for every
integer `t`, since `(t : ℚ).den = 1` unconditionally.) -/
theorem logRatio_int_lt (t : ℤ) (ht : 2 ≤ t) :
    Real.log (((t : ℚ)).den : ℝ) / Real.log (((t : ℚ)).num : ℝ) < 1 / 2 - 1 / Real.pi ^ 2 := by
  rw [Rat.den_intCast t]
  simp only [Nat.cast_one, Real.log_one, zero_div]
  have hpos : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have h : 1 / Real.pi ^ 2 < 1 / 2 := by
    rw [div_lt_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_gt_three]
  linarith

end Reduce

end QHarm

namespace QHarmonicRationalBase

open Real

/-- **The main statement.** Let `t > 1` be rational, written in lowest terms as
`t = t.num / t.den`. If `log t.den / log t.num < 1/2 − 1/π²`, then the `q`-harmonic
series `∑_{n≥1} 1/(tⁿ − 1)` is irrational. -/
theorem irrational_of_logRatio_lt (t : ℚ) (ht : 1 < t)
    (hθ : Real.log (t.den : ℝ) / Real.log (t.num : ℝ) < 1 / 2 - 1 / Real.pi ^ 2) :
    Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)) :=
  QHarm.master_rat t ht hθ

/-- **The first new bases, concretely.** For every odd `P ≥ 7` the series
`∑_{n≥1} 1/((P/2)ⁿ − 1)` is irrational. -/
theorem irrational_half_odd (P : ℕ) (hodd : Odd P) (hP : 7 ≤ P) :
    Irrational (∑' n : ℕ+, 1 / (((P : ℝ) / 2) ^ (n : ℕ) - 1)) := by
  have key := QHarm.master_rat ((P : ℚ) / 2) (QHarm.Reduce.one_lt_half_odd P hP) (by
    rw [QHarm.Reduce.num_half_odd P hodd, QHarm.Reduce.den_half_odd P hodd]
    push_cast
    exact QHarm.Reduce.log_two_div_log_lt hP)
  rwa [QHarm.Reduce.cast_half_odd P] at key

/-- **The integer case**, `Q = 1`: Erdős 1948. -/
theorem irrational_int (t : ℤ) (ht : 2 ≤ t) :
    Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)) :=
  QHarm.master_int t ht

end QHarmonicRationalBase

/-! ## Acceptance test

Each `example` below restates the conclusion of the corresponding theorem of
the Palomar Challenge file for this entry **verbatim** and is closed by a bare
term — no `by`, no coercion massaging. If any of the three statements had drifted from
the Challenge spelling (a stray `Rat.cast`, an `ℕ+` coercion, a different `1/2 − 1/π²`
elaboration), these would fail to elaborate. -/
section AcceptanceTest

open Real in
example : ∀ (t : ℚ), 1 < t →
    Real.log (t.den : ℝ) / Real.log (t.num : ℝ) < 1 / 2 - 1 / Real.pi ^ 2 →
    Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)) :=
  QHarmonicRationalBase.irrational_of_logRatio_lt

open Real in
example : ∀ (P : ℕ), Odd P → 7 ≤ P →
    Irrational (∑' n : ℕ+, 1 / (((P : ℝ) / 2) ^ (n : ℕ) - 1)) :=
  QHarmonicRationalBase.irrational_half_odd

open Real in
example : ∀ (t : ℤ), 2 ≤ t →
    Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)) :=
  QHarmonicRationalBase.irrational_int

end AcceptanceTest

#print axioms QHarmonicRationalBase.irrational_of_logRatio_lt
#print axioms QHarmonicRationalBase.irrational_half_odd
#print axioms QHarmonicRationalBase.irrational_int
