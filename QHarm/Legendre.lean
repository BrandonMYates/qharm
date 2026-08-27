/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QHarm.QBinom

/-!
# QHarm/Legendre.lean — the little q-Legendre objects (definitions only)

This file holds **only the definitions** of Van Assche's
`P_n` and `Q_n` (his equations (23) and (25)) together with the q-Pochhammer factor they
use, so that `QHarm/Orthogonality.lean`, `QHarm/LegendreBounds.lean` and
`QHarm/Integrality.lean` can be built in parallel against a fixed shared surface.

## Consumes

`QHarm/QBinom.lean` — `gauss` (the real one-variable Gaussian binomial) and its bounds.

## Normalisation — read this before using anything here

Van Assche works with `0 < q < 1` and evaluates at `x = t^n` where `t = 1/q`. Working
directly with `q` forces negative powers of `t` everywhere. Instead everything here is in
`t`-normalisation with the substitution `w = x / t^n` already performed:

* `legCoef t n j = (-1)^j t^{C(j,2)} [n,j]_t [n+j,n]_t` — **all exponents are natural
  numbers and no inverses appear**;
* `legG t n w = ∑_{j≤n} legCoef t n j · w^j`, so that Van Assche's `P_n(x | 1/t)` is
  `legG t n (x / t^n)`;
* in particular `legVal t n = legG t n 1 = P_n(t^n | 1/t)`, which is eq. (23), and the
  lattice values are `P_n(q^k | 1/t) = legG t n (t⁻¹^k · (t^n)⁻¹)`.

`Nat.choose j 2 = j(j-1)/2` is used for the triangular exponents; it is exact and dodges
ℕ-division in the exponent.

## Main results

Definitions only: `qpoch`, `legCoef`, `legG`, `legVal`, `legGamma`, `legQval`, `headSum`,
plus the unfolding lemmas and the `n = 0` base values.

`legG t n w = ∑_j legCoef t n j w^j` and `P_n(x|1/t) = ∑_j legGamma t n j x^j`; the two are
related by `legGamma t n j = legCoef t n j / (t^n)^j`, i.e. `P_n(x) = legG t n (x/t^n)`.

## What is NOT here

* the orthogonality of `legG` — `QHarm/Orthogonality.lean`;
* any size bound on `legVal` — `QHarm/LegendreBounds.lean`;
* integrality of `D_n · legVal` and `D_n · legQval` — `QHarm/Integrality.lean`;
* the clearing factor `D_n` itself — `QHarm/Clearing.lean`;
* the Padé identity (22) and the linear forms `A_n`, `B_n` — `QHarm/Forms.lean`.
-/

namespace QHarm

/-- The q-Pochhammer factor `(a; t)_m = ∏_{j<m} (1 - a t^j)`.

Mathlib has no q-Pochhammer machinery at all (only a TODO in
`RingTheory/Polynomial/Pochhammer.lean`), so this is defined here. -/
noncomputable def qpoch (t a : ℝ) (m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range m, (1 - a * t ^ j)

@[simp] theorem qpoch_zero (t a : ℝ) : qpoch t a 0 = 1 := by
  simp [qpoch]

theorem qpoch_succ (t a : ℝ) (m : ℕ) :
    qpoch t a (m + 1) = qpoch t a m * (1 - a * t ^ m) := by
  simp [qpoch, Finset.prod_range_succ]

/-- The `j`-th coefficient of the little q-Legendre polynomial in `t`-normalisation:
`(-1)^j t^{C(j,2)} [n,j]_t [n+j,n]_t`. -/
noncomputable def legCoef (t : ℝ) (n j : ℕ) : ℝ :=
  (-1) ^ j * t ^ (j.choose 2) * gauss t n j * gauss t (n + j) n

/-- The little q-Legendre polynomial `P_n(· | 1/t)` written in the rescaled variable
`w = x / t^n`. Van Assche's `P_n(x | q)` with `q = 1/t` is `legG t n (x / t^n)`. -/
noncomputable def legG (t : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), legCoef t n j * w ^ j

/-- `P_n(t^n | 1/t)` — Van Assche's equation (23), and the value the whole construction is
built on. -/
noncomputable def legVal (t : ℝ) (n : ℕ) : ℝ := legG t n 1

theorem legVal_eq (t : ℝ) (n : ℕ) :
    legVal t n = ∑ j ∈ Finset.range (n + 1), legCoef t n j := by
  simp [legVal, legG]

/-- The coefficient of `x^j` in `P_n(x | 1/t)` itself (as opposed to in the rescaled
variable `w`): `legGamma t n j = legCoef t n j / (t^n)^j`. -/
noncomputable def legGamma (t : ℝ) (n j : ℕ) : ℝ :=
  legCoef t n j * ((t ^ n) ^ j)⁻¹

/-- `Q_n(t^n | 1/t)`, the associated function of the second kind.

**Campaign deviation D5.** Van Assche's equation (25) gives `Q_n` as an explicit double sum
over Gaussian binomials and q-Pochhammers. We do not use it. `Q_n` is defined instead by
its defining property,

    Q_n(z) = ∑_{k≥0} q^k · (P_n(z) - P_n(q^k)) / (z - q^k),

expanded with `(z^j - x^j)/(z - x) = ∑_{i<j} z^i x^{j-1-i}` and the geometric sum
`∑_k q^{k(j-i)} = t^{j-i}/(t^{j-i} - 1)`. Two consequences:

* the Padé identity (22) becomes near-trivial rather than a q-series theorem, because
  `P_n(z) f(z) - Q_n(z) = ∑_k q^k P_n(q^k)/(z - q^k)` is now an add-and-subtract;
* the only denominators are `t^m - 1` with `1 ≤ m ≤ n`, so `QHarm/Clearing.lean`'s crude
  `D_n` clears `Q_n` too.

Nothing downstream mentions `Q_n` except through `A_n`, and the advertised theorems do not
mention it at all, so this definition is free to be chosen for convenience. It was checked
against equation (25) exactly (Python `Fraction`s, `t ∈ {2,3,5}`, `n = 1..8`): **the two
agree identically at every point tested**, and `D_n · Q_n ∈ ℤ` at every point tested. -/
noncomputable def legQval (t : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), legGamma t n j *
    ∑ i ∈ Finset.range j, (t ^ n) ^ i * (t ^ (j - i) / (t ^ (j - i) - 1))

/-- `P_n` at the lattice point `q^k`, `q = t⁻¹`. Lifted here at
integration time: `QHarm/Pade.lean` and `QHarm/CoefBound.lean` were built in parallel and
each defined this identically, which collides on import. -/
noncomputable def latVal (t : ℝ) (n k : ℕ) : ℝ := legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹)

/-- The head of the series, `∑_{k=1}^{n-1} 1/(t^k - 1)`, written over `Finset.range` so that
`QHarm/Basic.lean`'s `S_sub_head` applies directly. -/
noncomputable def headSum (t : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n - 1), 1 / (t ^ (k + 1) - 1)

@[simp] theorem headSum_zero (t : ℝ) : headSum t 0 = 0 := by
  simp [headSum]

@[simp] theorem headSum_one (t : ℝ) : headSum t 1 = 0 := by
  simp [headSum]

theorem legG_zero (t : ℝ) (w : ℝ) : legG t 0 w = 1 := by
  simp [legG, legCoef, gauss]

@[simp] theorem legVal_zero (t : ℝ) : legVal t 0 = 1 := legG_zero t 1

@[simp] theorem legQval_zero (t : ℝ) : legQval t 0 = 0 := by
  simp [legQval]

end QHarm
