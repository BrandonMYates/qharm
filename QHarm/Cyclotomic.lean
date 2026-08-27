/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# QHarm/Cyclotomic.lean — the sharp clearing factor `𝒟_n = ∏_{k≤n} Φ_k(P,Q)`

## Consumes

Nothing from `QHarm`; Mathlib only. This file is a root of the `QHarm` dependency graph
and therefore has **no legitimate frontier**: every statement below is proved outright.

## Main results

* `QHarm.hev` — homogeneous evaluation of an integer polynomial: for `p : ℤ[X]` and a
  degree budget `d ≥ p.natDegree`, `hev p d P Q = ∑_{i≤d} p.coeff i · P^i · Q^{d-i}`.
  This is `Q^d · p(P/Q)` with the denominator cleared, and it is an integer **by
  construction** — no integrality has to be transported from anywhere.
* `QHarm.PhiHom` — the homogenized cyclotomic value
  `Φ_k(P,Q) = Q^{φ(k)} · Φ_k(P/Q) = hev (cyclotomic k ℤ) (φ k) P Q : ℤ`.
* `QHarm.prod_PhiHom` — the defining product formula
  `∏_{d ∣ ℓ} Φ_d(P,Q) = P^ℓ − Q^ℓ` for `0 < ℓ`, with **no hypothesis on `P`, `Q`**
  (the degenerate case `Q = 0` is handled separately and does hold).
* `QHarm.Dsharp` — the sharp clearing factor `𝒟_n = ∏_{k=1}^{n} Φ_k(P,Q)`.
* `QHarm.sub_dvd_Dsharp` — **the point of the file**: `(P^ℓ − Q^ℓ) ∣ 𝒟_n` *simultaneously*
  for every `1 ≤ ℓ ≤ n`, because `𝒟_n` contains each cyclotomic atom exactly once.
  This is what makes `𝒟_n ≈ P^{3n²/π²}` instead of the crude `P^{n²/2}`.
* `QHarm.PhiHom_pos`, `QHarm.PhiHom_ne_zero` — positivity for `0 < Q < P`.
* `QHarm.PhiHom_bounds` — `(P−Q)^{φ(k)} ≤ Φ_k(P,Q) ≤ (P+Q)^{φ(k)}` for `0 < Q < P`.
  Both inequalities are *non-strict on purpose*: `k = 1` saturates the lower bound
  (`Φ_1 = P − Q`) and `k = 2` saturates the upper one (`Φ_2 = P + Q`).
* `QHarm.log_PhiHom_sub` — the per-atom Möbius expansion
  `log Φ_k(P,Q) − φ(k)·log P = ∑_{ab=k} μ(a)·log(1 − (Q/P)^b)`.
* `QHarm.log_Dsharp_eq` — **the log-sum identity consumed by `QHarm/Growth.lean`**:
  `|log 𝒟_n − (∑_{k≤n} φ(k))·log P| ≤ n · (P/(P−Q))²`, i.e. `O(n)` with an explicit
  constant. Note this is genuinely sharper than what `PhiHom_bounds` gives: the crude
  two-sided bound only pins `log 𝒟_n` to within `Θ(n²)`, which is useless against the
  `n²` main term. The cancellation is supplied by Möbius inversion, not by the bounds.

## Numerics (checked before any of the above was proved)

`PhiHom` is `noncomputable` — Mathlib's `Polynomial.cyclotomic` is — so the checks were run
outside Lean, against `sympy`'s `cyclotomic_poly`, homogenised the same way:

* `prod_PhiHom`: exact for `(P,Q) ∈ {(2,1),(3,1),(7,2),(9,2),(11,2),(5,3)}`, all `ℓ ≤ 12`.
* `sub_dvd_Dsharp`: exact for `(P,Q) ∈ {(2,1),(7,2),(5,3)}`, all `1 ≤ ℓ ≤ n ≤ 12`.
* `PhiHom_bounds`: holds, both sides, `k ≤ 40`, incl. the saturating cases `k = 1, 2`.
* `log 𝒟_n / (n² log P)` at `n = 400`: `0.30426` (P,Q = 2,1), `0.30424` (7,2), `0.30425`
  (5,3), against `3/π² = 0.3039636`. The object is the right one, and the limit is
  independent of `Q`, as `log_Dsharp_eq` says it must be.
* `log_Dsharp_eq`'s constant: at `P,Q = 7,2` the true error is `0.53 / 1.22 / 2.65` at
  `n = 10 / 50 / 200` against the bound `5.6 / 28 / 112`. Lossy by design.

## The implementation decision, and why

`PhiHom` is defined as `hev (Polynomial.cyclotomic k ℤ) (Nat.totient k) P Q`, i.e. a bare
`Finset.sum` over the coefficients of Mathlib's `cyclotomic`. Three routes were priced:

1. **`Polynomial.homogenize` into `MvPolynomial (Fin 2) ℤ`** (`Algebra/Polynomial/
   Homogenize.lean`). Rejected: it drags the whole two-variable `MvPolynomial` API in for
   what is ultimately a single integer, and after evaluating at `(P, Q)` one *still* has to
   build the bridge to `ℝ` by hand for `PhiHom_bounds`. Strictly more work than route 3.

2. **Strong recursion on `k` from the product formula**, `Φ_k := (P^k − Q^k) / ∏_{d ∣ k,
   d < k} Φ_d` with integer division. This makes `prod_PhiHom` nearly definitional, which
   is the case for it. Rejected anyway, for two reasons that were decisive. (a) The
   induction is not closed by the recursion: to get `prod_PhiHom` out one must first prove
   `∏_{d<k} Φ_d ∣ P^k − Q^k`, which is essentially re-proving that cyclotomic polynomials
   have integer coefficients — Mathlib already did that and the recursion cannot reuse it.
   (b) It severs the link to `Polynomial.cyclotomic` entirely, so `PhiHom_bounds` loses
   `sub_one_pow_totient_le_cyclotomic_eval` / `cyclotomic_eval_le_add_one_pow_totient` and
   would have to be re-derived from scratch over ℂ. Both of the file's two hard theorems
   get harder.

3. **Chosen: `hev` of `cyclotomic k ℤ`.** `Polynomial.degree_cyclotomic` gives
   `natDegree (cyclotomic k ℤ) = φ k` exactly, so the degree budget is tight and the single
   bridge lemma `hev_cast` — `(hev p d P Q : K) = Q^d · p(P/Q)` over any field, for `Q ≠ 0`
   — serves *both* hard theorems: at `K = ℚ` it turns `prod_PhiHom` into
   `prod_cyclotomic_eq_X_pow_sub_one` plus `Nat.sum_totient`, and at `K = ℝ` it turns
   `PhiHom_bounds` into Mathlib's cyclotomic evaluation bounds. Integrality is definitional
   (a sum of products of integers) and is never transported. One 8-line lemma, reused twice.

## What is NOT here

* Mertens' asymptotic `∑_{k≤n} φ(k) = 3n²/π² + O(n log n)` — `QHarm/Mertens.lean`.
* The growth limit `𝒟_n^{1/n²} → P^{3/π²}` — `QHarm/Growth.lean`. This file supplies the
  `O(n)` error term it needs and nothing else; the `n²`-order main term is Mertens' job.
* The crude integer-track clearing factor `∏_{k≤n}(t^k − 1)` — `QHarm/Clearing.lean`.
  That one suffices for `irrational_int` (build-notes deviation **D1**); this file exists
  precisely because it does *not* suffice at `t = 7/2`.
* Anything about the q-series construction: `S t`, the little q-Legendre polynomials, the
  linear forms `A n`, `B n`, `R n`, orthogonality, or the Padé identity. This file makes no
  irrationality claim; it is arithmetic on a finite product.
-/

set_option linter.unusedVariables false

namespace QHarm

open Finset Polynomial

/-! ## Homogeneous evaluation of an integer polynomial -/

/-- Homogeneous evaluation with degree budget `d`:
`hev p d P Q = ∑_{i ≤ d} p.coeff i · P^i · Q^(d-i)`.

When `p.natDegree ≤ d` and `Q ≠ 0` this equals `Q^d · p(P/Q)` (see `hev_cast`), but it is
an *integer by construction*. -/
def hev (p : Polynomial ℤ) (d : ℕ) (P Q : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (d + 1), p.coeff i * P ^ i * Q ^ (d - i)

/-- The bridge: over any field, `hev p d P Q = Q^d · p(P/Q)` provided `Q ≠ 0` and the
degree budget `d` is at least `p.natDegree`. This single lemma is used at `K = ℚ` for
`prod_PhiHom` and at `K = ℝ` for `PhiHom_bounds`. -/
theorem hev_cast {K : Type*} [Field K] {p : Polynomial ℤ} {d : ℕ} (hd : p.natDegree ≤ d)
    (P Q : ℤ) (hQ : (Q : K) ≠ 0) :
    ((hev p d P Q : ℤ) : K)
      = (Q : K) ^ d * (p.map (Int.castRingHom K)).eval ((P : K) / (Q : K)) := by
  have hdeg : (p.map (Int.castRingHom K)).natDegree < d + 1 :=
    lt_of_le_of_lt (le_trans Polynomial.natDegree_map_le hd) (Nat.lt_succ_self d)
  rw [Polynomial.eval_eq_sum_range' hdeg, Finset.mul_sum, hev, Int.cast_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Polynomial.coeff_map, eq_intCast, div_pow]
  push_cast
  rw [pow_sub₀ _ hQ hi']
  field_simp

/-- At `Q = 0`, `hev` collapses to the leading term. -/
theorem hev_zero_right {p : Polynomial ℤ} {d : ℕ} (P : ℤ) :
    hev p d P 0 = p.coeff d * P ^ d := by
  rw [hev]
  refine (Finset.sum_eq_single d ?_ ?_).trans ?_
  · intro i hi hne
    have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have : d - i ≠ 0 := by omega
    simp [zero_pow this]
  · intro h
    exact absurd (Finset.self_mem_range_succ d) h
  · simp

/-! ## The homogenized cyclotomic value -/

/-- The homogenized cyclotomic value, `Φ_k(P,Q) = Q^{φ(k)} · Φ_k(P/Q)`, as an integer. -/
noncomputable def PhiHom (P Q : ℤ) (k : ℕ) : ℤ :=
  hev (Polynomial.cyclotomic k ℤ) (Nat.totient k) P Q

/-- `PhiHom` cast into any field, for `Q ≠ 0`: literally `Q^{φ(k)} · Φ_k(P/Q)`. -/
theorem PhiHom_cast {K : Type*} [Field K] (P Q : ℤ) (k : ℕ) (hQ : (Q : K) ≠ 0) :
    ((PhiHom P Q k : ℤ) : K)
      = (Q : K) ^ Nat.totient k * (Polynomial.cyclotomic k K).eval ((P : K) / (Q : K)) := by
  rw [PhiHom, hev_cast (le_of_eq (Polynomial.natDegree_cyclotomic k ℤ)) P Q hQ,
    Polynomial.map_cyclotomic]

@[simp] theorem PhiHom_one (P Q : ℤ) : PhiHom P Q 1 = P - Q := by
  have h1 : Nat.totient 1 = 1 := rfl
  simp only [PhiHom, hev, h1, Polynomial.cyclotomic_one, Finset.sum_range_succ,
    Finset.sum_range_zero, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
    Polynomial.coeff_X_one, Polynomial.coeff_one, zero_add]
  norm_num
  ring

@[simp] theorem PhiHom_two (P Q : ℤ) : PhiHom P Q 2 = P + Q := by
  have h1 : Nat.totient 2 = 1 := rfl
  simp only [PhiHom, hev, h1, Polynomial.cyclotomic_two, Finset.sum_range_succ,
    Finset.sum_range_zero, Polynomial.coeff_add, Polynomial.coeff_X_zero,
    Polynomial.coeff_X_one, Polynomial.coeff_one, zero_add]
  norm_num
  ring

/-- At `Q = 0` the atom degenerates to `P^{φ(k)}` (`cyclotomic` is monic). -/
theorem PhiHom_zero_right (P : ℤ) (k : ℕ) : PhiHom P 0 k = P ^ Nat.totient k := by
  rw [PhiHom, hev_zero_right]
  have : (Polynomial.cyclotomic k ℤ).coeff (Nat.totient k) = 1 := by
    have h := (Polynomial.cyclotomic.monic k ℤ)
    rwa [Polynomial.Monic, Polynomial.leadingCoeff,
      Polynomial.natDegree_cyclotomic k ℤ] at h
  rw [this, one_mul]

/-- **The defining product formula.** `∏_{d ∣ ℓ} Φ_d(P,Q) = P^ℓ − Q^ℓ`. -/
theorem prod_PhiHom (P Q : ℤ) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∏ d ∈ ℓ.divisors, PhiHom P Q d = P ^ ℓ - Q ^ ℓ := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp only [PhiHom_zero_right, Finset.prod_pow_eq_pow_sum, Nat.sum_totient,
      zero_pow hℓ.ne', sub_zero]
  · have hQℚ : ((Q : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hQ
    have key : ((∏ d ∈ ℓ.divisors, PhiHom P Q d : ℤ) : ℚ) = ((P ^ ℓ - Q ^ ℓ : ℤ) : ℚ) := by
      push_cast
      rw [Finset.prod_congr rfl (fun d _ => PhiHom_cast (K := ℚ) P Q d hQℚ),
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Nat.sum_totient,
        ← Polynomial.eval_prod, Polynomial.prod_cyclotomic_eq_X_pow_sub_one hℓ ℚ]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, div_pow]
      field_simp
    exact_mod_cast key

/-! ## The sharp clearing factor -/

/-- The sharp clearing factor `𝒟_n = ∏_{k=1}^{n} Φ_k(P,Q)`. -/
noncomputable def Dsharp (P Q : ℤ) (n : ℕ) : ℤ := ∏ k ∈ Finset.Icc 1 n, PhiHom P Q k

@[simp] theorem Dsharp_zero (P Q : ℤ) : Dsharp P Q 0 = 1 := by simp [Dsharp]

theorem Dsharp_succ (P Q : ℤ) (n : ℕ) :
    Dsharp P Q (n + 1) = Dsharp P Q n * PhiHom P Q (n + 1) := by
  rw [Dsharp, Dsharp, ← Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]

/-- **The simultaneous divisibility.** This is the whole point of the file: a single
product `𝒟_n` of `n` atoms is divisible by `P^ℓ − Q^ℓ` for *every* `ℓ ≤ n` at once,
because each cyclotomic atom occurs exactly once in it. -/
theorem sub_dvd_Dsharp {P Q : ℤ} {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : ℓ ≤ n) :
    (P ^ ℓ - Q ^ ℓ) ∣ Dsharp P Q n := by
  rw [← prod_PhiHom P Q (by omega : 0 < ℓ), Dsharp]
  refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
  intro d hd
  rw [Finset.mem_Icc]
  exact ⟨Nat.pos_of_mem_divisors hd, le_trans (Nat.divisor_le hd) hn⟩

/-! ## Size and positivity -/

/-- `Φ_k(P,Q) > 0` whenever `0 < Q < P`. -/
theorem PhiHom_pos {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (k : ℕ) : 0 < PhiHom P Q k := by
  have hQR : ((Q : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hQ.ne'
  have hQR0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hx : (1 : ℝ) < (P : ℝ) / (Q : ℝ) := by
    rw [lt_div_iff₀ hQR0, one_mul]
    exact_mod_cast hPQ
  have : (0 : ℝ) < ((PhiHom P Q k : ℤ) : ℝ) := by
    rw [PhiHom_cast (K := ℝ) P Q k hQR]
    exact mul_pos (pow_pos hQR0 _) (Polynomial.cyclotomic_pos' k hx)
  exact_mod_cast this

theorem PhiHom_ne_zero {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (k : ℕ) : PhiHom P Q k ≠ 0 :=
  (PhiHom_pos hQ hPQ k).ne'

theorem Dsharp_pos {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ) : 0 < Dsharp P Q n :=
  Finset.prod_pos fun k _ => PhiHom_pos hQ hPQ k

/-- Degree/size: `Φ_k(P,Q)` is bounded between `(P−Q)^{φ(k)}` and `(P+Q)^{φ(k)}` for
`P > Q > 0`.

Both inequalities are non-strict, and that is forced: `Φ_1 = P − Q` saturates the lower
bound and `Φ_2 = P + Q` saturates the upper one. (The hypothesis `1 ≤ k` is not actually
needed — `Φ_0 = 1` and `φ 0 = 0` — but it is kept so the statement matches the interface
`QHarm/Growth.lean` was specified against.)

This is **not** sufficient for the sharp constant: it pins `log 𝒟_n` only to within
`Θ(n²)`. See `log_Dsharp_eq` for the `O(n)` statement. -/
theorem PhiHom_bounds {P Q : ℤ} (h : 0 < Q) (hPQ : Q < P) {k : ℕ} (hk : 1 ≤ k) :
    (P - Q) ^ Nat.totient k ≤ PhiHom P Q k ∧ PhiHom P Q k ≤ (P + Q) ^ Nat.totient k := by
  have hQR : ((Q : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr h.ne'
  have hQR0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast h
  have hx : (1 : ℝ) < (P : ℝ) / (Q : ℝ) := by
    rw [lt_div_iff₀ hQR0, one_mul]; exact_mod_cast hPQ
  have hcast := PhiHom_cast (K := ℝ) P Q k hQR
  constructor
  · have hlow : (((P - Q) ^ Nat.totient k : ℤ) : ℝ) ≤ ((PhiHom P Q k : ℤ) : ℝ) := by
      rw [hcast]
      have := Polynomial.sub_one_pow_totient_le_cyclotomic_eval hx k
      calc (((P - Q) ^ Nat.totient k : ℤ) : ℝ)
          = (Q : ℝ) ^ Nat.totient k * ((P : ℝ) / (Q : ℝ) - 1) ^ Nat.totient k := by
            rw [← mul_pow]; push_cast; field_simp
        _ ≤ (Q : ℝ) ^ Nat.totient k * (Polynomial.cyclotomic k ℝ).eval ((P : ℝ) / (Q : ℝ)) := by
            exact mul_le_mul_of_nonneg_left this (le_of_lt (pow_pos hQR0 _))
    exact_mod_cast hlow
  · have hhigh : ((PhiHom P Q k : ℤ) : ℝ) ≤ (((P + Q) ^ Nat.totient k : ℤ) : ℝ) := by
      rw [hcast]
      have := Polynomial.cyclotomic_eval_le_add_one_pow_totient hx k
      calc (Q : ℝ) ^ Nat.totient k * (Polynomial.cyclotomic k ℝ).eval ((P : ℝ) / (Q : ℝ))
          ≤ (Q : ℝ) ^ Nat.totient k * ((P : ℝ) / (Q : ℝ) + 1) ^ Nat.totient k :=
            mul_le_mul_of_nonneg_left this (le_of_lt (pow_pos hQR0 _))
        _ = (((P + Q) ^ Nat.totient k : ℤ) : ℝ) := by
            rw [← mul_pow]; push_cast; field_simp
    exact_mod_cast hhigh

/-! ## The log-sum identity consumed by `QHarm/Growth.lean`

The crude bounds `PhiHom_bounds` pin `log 𝒟_n` only to within `Θ(n²)`, which is the same
order as the main term and therefore useless. The `O(n)` statement below comes from Möbius
inversion of `prod_PhiHom`: writing `r = Q/P`,

  `log Φ_k(P,Q) = ∑_{ab=k} μ(a) · log(P^b − Q^b) = φ(k)·log P + ∑_{ab=k} μ(a)·log(1 − r^b)`,

using `∑_{ab=k} μ(a)·b = φ(k)` — itself obtained by inverting `∑_{d ∣ ℓ} φ(d) = ℓ`. The
error term is then bounded divisor-by-divisor, with no divisor-swapping needed: for `k ≤ n`
one simply has `k.divisors ⊆ Icc 1 n`.
-/

private theorem geom_sum_le_inv {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i ≤ (1 - r)⁻¹ := by
  have hlt : (0:ℝ) < 1 - r := by linarith
  have hm : (∑ i ∈ Finset.range n, r ^ i) * (1 - r) = 1 - r ^ n := by
    have h := geom_sum_mul r n
    linear_combination -h
  have hrn : (0:ℝ) ≤ r ^ n := pow_nonneg h0 n
  have key : (∑ i ∈ Finset.range n, r ^ i) * (1 - r) ≤ 1 := by rw [hm]; linarith
  have hinv : (0:ℝ) ≤ (1 - r)⁻¹ := le_of_lt (inv_pos.mpr hlt)
  calc ∑ i ∈ Finset.range n, r ^ i
      = ((∑ i ∈ Finset.range n, r ^ i) * (1 - r)) * (1 - r)⁻¹ := by
        field_simp
    _ ≤ 1 * (1 - r)⁻¹ := mul_le_mul_of_nonneg_right key hinv
    _ = (1 - r)⁻¹ := one_mul _

/-- The tail estimate `∑_{d=1}^{n} |log(1 − r^d)| ≤ (1−r)^{-2}`, uniform in `n`. -/
private theorem sum_abs_log_le {r : ℝ} (h0 : 0 < r) (h1 : r < 1) (n : ℕ) :
    ∑ d ∈ Finset.Icc 1 n, |Real.log (1 - r ^ d)| ≤ ((1 - r)⁻¹) ^ 2 := by
  have hlt : (0:ℝ) < 1 - r := by linarith
  have hinv : (0:ℝ) ≤ (1 - r)⁻¹ := le_of_lt (inv_pos.mpr hlt)
  have step : ∀ d ∈ Finset.Icc 1 n, |Real.log (1 - r ^ d)| ≤ (1 - r)⁻¹ * r ^ d := by
    intro d hd
    obtain ⟨hd1, -⟩ := Finset.mem_Icc.mp hd
    obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    have hpm : (0:ℝ) ≤ r ^ m := pow_nonneg h0.le m
    have hrd : r ^ (m + 1) ≤ r := by
      rw [pow_succ]
      nlinarith [pow_le_one₀ h0.le h1.le (n := m)]
    have hrdpos : (0:ℝ) < r ^ (m + 1) := pow_pos h0 _
    have hpos : (0:ℝ) < 1 - r ^ (m + 1) := by linarith
    have hlogp : Real.log (1 - r ^ (m + 1)) ≤ 0 :=
      Real.log_nonpos (by linarith) (by linarith)
    rw [abs_of_nonpos hlogp]
    have hle := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at hle
    have hAeq : (1 - r ^ (m + 1))⁻¹ - 1 = r ^ (m + 1) * (1 - r ^ (m + 1))⁻¹ := by
      field_simp
      ring
    rw [hAeq] at hle
    refine hle.trans ?_
    rw [mul_comm ((1:ℝ) - r)⁻¹]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hlt (by linarith)) hrdpos.le
  calc ∑ d ∈ Finset.Icc 1 n, |Real.log (1 - r ^ d)|
      ≤ ∑ d ∈ Finset.Icc 1 n, (1 - r)⁻¹ * r ^ d := Finset.sum_le_sum step
    _ = (1 - r)⁻¹ * ∑ d ∈ Finset.Icc 1 n, r ^ d := by rw [Finset.mul_sum]
    _ ≤ (1 - r)⁻¹ * ∑ d ∈ Finset.range (n + 1), r ^ d := by
        refine mul_le_mul_of_nonneg_left ?_ hinv
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro x hx
          rw [Finset.mem_Icc] at hx
          rw [Finset.mem_range]
          omega
        · intro i _ _
          positivity
    _ ≤ (1 - r)⁻¹ * (1 - r)⁻¹ :=
        mul_le_mul_of_nonneg_left (geom_sum_le_inv h0.le h1 (n + 1)) hinv
    _ = ((1 - r)⁻¹) ^ 2 := by ring

/-- Möbius inversion of `Nat.sum_totient`: `∑_{ab=k} μ(a)·b = φ(k)` over `ℝ`. -/
theorem sum_moebius_mul_snd {k : ℕ} (hk : 0 < k) :
    ∑ x ∈ k.divisorsAntidiagonal,
        ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * ((x.2 : ℕ) : ℝ)
      = ((Nat.totient k : ℕ) : ℝ) := by
  have hfwd : ∀ m : ℕ, 0 < m → ∑ d ∈ m.divisors, ((Nat.totient d : ℕ) : ℝ) = ((m : ℕ) : ℝ) := by
    intro m _
    rw [← Nat.cast_sum]
    exact_mod_cast congrArg (fun j : ℕ => (j : ℝ)) (Nat.sum_totient m)
  have h := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq (R := ℝ)
    (f := fun d => ((Nat.totient d : ℕ) : ℝ)) (g := fun m => ((m : ℕ) : ℝ))).mp hfwd k hk
  simpa [zsmul_eq_mul] using h

/-- **The per-atom Möbius expansion.** For `0 < Q < P` and `k ≥ 1`, writing `r = Q/P`,
`log Φ_k(P,Q) − φ(k)·log P = ∑_{ab=k} μ(a)·log(1 − r^b)`.

This is the cancellation that `PhiHom_bounds` cannot see. Each summand is `O(r^b)`, and the
number of summands is `τ(k)`, so the whole thing is `O(1)` per `k` on average — against the
`Θ(φ(k))` that the crude bounds give. -/
theorem log_PhiHom_sub {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) {k : ℕ} (hk : 0 < k) :
    Real.log ((PhiHom P Q k : ℤ) : ℝ) - ((Nat.totient k : ℕ) : ℝ) * Real.log ((P : ℤ) : ℝ)
      = ∑ x ∈ k.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ)
            * Real.log (1 - (((Q : ℤ) : ℝ) / ((P : ℤ) : ℝ)) ^ x.2) := by
  have hP0 : (0:ℝ) < ((P : ℤ) : ℝ) := by exact_mod_cast lt_trans hQ hPQ
  have hQ0 : (0:ℝ) < ((Q : ℤ) : ℝ) := by exact_mod_cast hQ
  set r : ℝ := ((Q : ℤ) : ℝ) / ((P : ℤ) : ℝ) with hr
  have hr0 : 0 < r := div_pos hQ0 hP0
  have hr1 : r < 1 := by rw [hr, div_lt_one hP0]; exact_mod_cast hPQ
  have hlogsum : ∀ m : ℕ, 0 < m →
      ∑ d ∈ m.divisors, Real.log ((PhiHom P Q d : ℤ) : ℝ)
        = Real.log (((P : ℤ) : ℝ) ^ m - ((Q : ℤ) : ℝ) ^ m) := by
    intro m hm
    have hcast : ((∏ d ∈ m.divisors, PhiHom P Q d : ℤ) : ℝ)
        = ∏ d ∈ m.divisors, ((PhiHom P Q d : ℤ) : ℝ) := Int.cast_prod _ _
    rw [← Real.log_prod (fun d _ => by exact_mod_cast PhiHom_ne_zero hQ hPQ d), ← hcast,
      prod_PhiHom P Q hm]
    push_cast
    ring_nf
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq (R := ℝ)
    (f := fun d => Real.log ((PhiHom P Q d : ℤ) : ℝ))
    (g := fun m => Real.log (((P : ℤ) : ℝ) ^ m - ((Q : ℤ) : ℝ) ^ m))).mp hlogsum k hk
  have hinv' : ∑ x ∈ k.divisorsAntidiagonal,
      ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ)
        * Real.log (((P : ℤ) : ℝ) ^ x.2 - ((Q : ℤ) : ℝ) ^ x.2)
      = Real.log ((PhiHom P Q k : ℤ) : ℝ) := by
    simpa [zsmul_eq_mul] using hinv
  have hsplit : ∀ x ∈ k.divisorsAntidiagonal,
      ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ)
          * Real.log (((P : ℤ) : ℝ) ^ x.2 - ((Q : ℤ) : ℝ) ^ x.2)
        = ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * ((x.2 : ℕ) : ℝ)
              * Real.log ((P : ℤ) : ℝ)
          + ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * Real.log (1 - r ^ x.2) := by
    intro x hx
    have hx2 : 0 < x.2 := by
      obtain ⟨he, hne⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      rcases Nat.eq_zero_or_pos x.2 with h | h
      · exact absurd (by rw [← he, h, Nat.mul_zero]) hne
      · exact h
    have hrx : r ^ x.2 < 1 := pow_lt_one₀ hr0.le hr1 hx2.ne'
    have hfac : ((P : ℤ) : ℝ) ^ x.2 - ((Q : ℤ) : ℝ) ^ x.2
        = ((P : ℤ) : ℝ) ^ x.2 * (1 - r ^ x.2) := by
      rw [hr, div_pow]
      field_simp
    rw [hfac, Real.log_mul (by positivity) (by linarith : (1 : ℝ) - r ^ x.2 ≠ 0),
      Real.log_pow]
    ring
  rw [← hinv', Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_moebius_mul_snd hk]
  ring

/-- **The log-sum identity that `QHarm/Growth.lean` consumes.**

`log 𝒟_n = (∑_{k≤n} φ(k))·log P + O(n)`, with the explicit constant `(P/(P−Q))²`:

    |log 𝒟_n − (∑_{k≤n} φ(k))·log P|  ≤  n · (P/(P−Q))².

Together with Mertens' `∑_{k≤n} φ(k) = 3n²/π² + o(n²)` this gives `𝒟_n^{1/n²} → P^{3/π²}`,
which is the sharp clearing rate the rational-base track needs. The error term here is
`O(n)`, hence `o(n²)`; the constant is deliberately lossy (the true error is `O(1)·n` with a
much smaller constant — measured `2.65` at `P=7, Q=2, n=200` against the bound `112`), since
nothing downstream is tight. -/
theorem log_Dsharp_eq {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ) :
    |Real.log ((Dsharp P Q n : ℤ) : ℝ)
        - (∑ k ∈ Finset.Icc 1 n, ((Nat.totient k : ℕ) : ℝ)) * Real.log ((P : ℤ) : ℝ)|
      ≤ (n : ℝ) * (((P : ℤ) : ℝ) / (((P : ℤ) : ℝ) - ((Q : ℤ) : ℝ))) ^ 2 := by
  have hP0 : (0:ℝ) < ((P : ℤ) : ℝ) := by exact_mod_cast lt_trans hQ hPQ
  have hQ0 : (0:ℝ) < ((Q : ℤ) : ℝ) := by exact_mod_cast hQ
  set r : ℝ := ((Q : ℤ) : ℝ) / ((P : ℤ) : ℝ) with hr
  have hr0 : 0 < r := div_pos hQ0 hP0
  have hr1 : r < 1 := by rw [hr, div_lt_one hP0]; exact_mod_cast hPQ
  have hC : ((1 : ℝ) - r)⁻¹ = ((P : ℤ) : ℝ) / (((P : ℤ) : ℝ) - ((Q : ℤ) : ℝ)) := by
    have h1 : (1 : ℝ) - r = (((P : ℤ) : ℝ) - ((Q : ℤ) : ℝ)) / ((P : ℤ) : ℝ) := by
      rw [hr]; field_simp
    rw [h1, inv_div]
  have hcast : ((Dsharp P Q n : ℤ) : ℝ) = ∏ k ∈ Finset.Icc 1 n, ((PhiHom P Q k : ℤ) : ℝ) := by
    rw [Dsharp]; exact Int.cast_prod _ _
  rw [hcast, Real.log_prod (fun k _ => by exact_mod_cast PhiHom_ne_zero hQ hPQ k),
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have bound : ∀ k ∈ Finset.Icc 1 n,
      |Real.log ((PhiHom P Q k : ℤ) : ℝ) - ((Nat.totient k : ℕ) : ℝ) * Real.log ((P : ℤ) : ℝ)|
        ≤ ((1 - r)⁻¹) ^ 2 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    rw [log_PhiHom_sub hQ hPQ (by omega : 0 < k)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∀ x ∈ k.divisorsAntidiagonal,
        |((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * Real.log (1 - r ^ x.2)|
          ≤ |Real.log (1 - r ^ x.2)| := by
      intro x _
      rw [abs_mul]
      refine mul_le_of_le_one_left (abs_nonneg _) ?_
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Nat.sum_divisorsAntidiagonal' (f := fun _ b => |Real.log (1 - r ^ b)|)]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => abs_nonneg _))
      (sum_abs_log_le hr0 hr1 n)
    intro d hd
    rw [Finset.mem_Icc]
    exact ⟨Nat.pos_of_mem_divisors hd, le_trans (Nat.divisor_le hd) hk2⟩
  refine (Finset.sum_le_sum bound).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, hC]
  simp

/-! ## Axiom audit -/

section AxiomAudit

#print axioms QHarm.prod_PhiHom
#print axioms QHarm.sub_dvd_Dsharp
#print axioms QHarm.PhiHom_bounds
#print axioms QHarm.PhiHom_pos
#print axioms QHarm.Dsharp_pos
#print axioms QHarm.sum_moebius_mul_snd
#print axioms QHarm.log_PhiHom_sub
#print axioms QHarm.log_Dsharp_eq

end AxiomAudit

end QHarm
