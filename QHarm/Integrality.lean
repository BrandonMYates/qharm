/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QHarm.CoefBound
import QHarm.Clearing

/-!
# QHarm/Integrality.lean — the cleared linear forms are integers (integer track)

## Consumes

* `QHarm/Legendre.lean` — `legCoef`, `legVal`, `legGamma`, `legQval`, `headSum`.
* `QHarm/QBinom.lean` — `qbin` (ℤ-valued by construction) and `gauss_eq_qbin`.
* `QHarm/Clearing.lean` — `Dz`, `Dr`, `Dr_eq_Dz`, `sub_one_dvd_Dz`.
* `QHarm/CoefBound.lean` — only `two_mul_choose_two_add`, a `Nat` bookkeeping lemma.

Every statement below is proved outright; there are **no frontiers** in this file.

## The clearing factor used here

Campaign deviation **D1** says the integer track needs no cyclotomic clearing. It needs one
thing beyond `D_n = ∏_{k=1}^n (t^k − 1)`, though: an extra power of `t`. Write

    Mexp n = n(n-1)/2 = C(n,2).

`legGamma t n j = legCoef t n j / (t^n)^j` carries a **negative** power of `t`, and the
`(j,d)` term of `legQval` (with `d = j - i`, `1 ≤ d ≤ j ≤ n`) is exactly

    legCoef t n j / (t^((n-1)*d) * (t^d - 1)).

`legCoef t n j` is `t^(C(j,2))` times an integer and no more: the Gaussian binomials have
constant term `1`, so their values are `≡ 1 (mod t)`. Hence `t^((n-1)*d) ∤ legCoef t n j`
whenever `(n-1)*d > C(j,2)`, which is the generic case — at `j = d = n` one needs `n(n-1)`
and has only `n(n-1)/2`. **`D_n · Q_n(t^n)` is nevertheless an integer** (checked exactly
with `Fraction`s, `t ∈ {2,3,5}`, `n ≤ 8`), but only through cancellation across the double
sum; that is not proved here and is not needed. Multiplying by the extra `t^(Mexp n)` makes
the statement **term-by-term** true, and `key_exp` is exactly the inequality that says so:

    (n-1)*d ≤ C(j,2) + Mexp n   for  1 ≤ d ≤ j ≤ n,

with equality precisely at `j = d = n`. So `t^(Mexp n)` is the smallest uniform extra power
that works. Cost to the balance: `t^(n(n-1)/2)` — and it is affordable. Measured exactly
(`Fraction`s for the forms, 6000-bit `mpmath` for `S`; `t ∈ {2,3,5}`, `n = 1..10`):

    log_t | t^(Mexp n) D_n (P_n(t^n) S - Q_n(t^n) - P_n(t^n) headSum) | / n²  →  -1/2 - 3/(2n)

i.e. the linear form is `≈ t^(-n²/2 - 3n/2)`, against a requirement of `< 1`. Without the
extra power it is `t^(-n² - n)`; the extra `t^(n(n-1)/2)` eats exactly half the `n²`
coefficient and leaves the other half. Smallest value tested is `t^(-2.09)` at `n = 1`,
so the bound holds at every `n ≥ 1`, not just asymptotically.

## Main results

* `Mexp`, `Mexp_eq_choose`, `two_mul_Mexp_add` — the extra exponent.
* `key_exp` — the exponent inequality above (`Nat`, division- and subtraction-safe).
* `coefZ t n j` — the integer `(-1)^j [n,j]_t [n+j,n]_t`, and
  `legCoef_eq_of_int : legCoef (t:ℝ) n j = t^(C(j,2)) * coefZ t n j`.
* `legVal_isInt` — `P_n(t^n) ∈ ℤ`. **No clearing factor needed at all.**
* `Dr_mul_legVal_mul_headSum_isInt` — `D_n · P_n(t^n) · headSum ∈ ℤ`. Also no extra
  `t`-power needed.
* `tM_Dr_mul_legQval_isInt` — `t^(Mexp n) · D_n · Q_n(t^n) ∈ ℤ`. This is the one that
  needs the extra power.
* `tM_Dr_mul_legVal_isInt`, `tM_Dr_mul_legVal_mul_headSum_isInt` — the same statements with
  the `t^(Mexp n) · D_n` clearing factor, for uniformity with the above.
* `tM_Dr_mul_Aform_isInt` — the combined form `t^(Mexp n) · D_n · (Q_n + P_n · headSum) ∈ ℤ`,
  i.e. integrality of `A_n`.

## What is NOT here

* `D_n · Q_n(t^n) ∈ ℤ` **without** the extra `t^(Mexp n)`. True (measured), unproved, and
  deliberately not attempted — see the discussion above.
* Any size bound on `D_n`, on `legVal`, or on the remainder — `QHarm/Clearing.lean`,
  `QHarm/CoefBound.lean`, `QHarm/Degree.lean`.
* The Padé identity, the linear forms `A_n`/`B_n` themselves, and the balance —
  `QHarm/Forms.lean`, `QHarm/Main.lean`.
* Anything about the general rational-base track (`Q ≠ 1`).
-/

namespace QHarm

open Finset

/-! ### The extra `t`-power -/

/-- The extra clearing exponent, `M n = n(n-1)/2`. -/
def Mexp (n : ℕ) : ℕ := n * (n - 1) / 2

theorem Mexp_eq_choose (n : ℕ) : Mexp n = n.choose 2 := (Nat.choose_two_right n).symm

/-- Subtraction-free form: `2 M n + n = n^2`. -/
theorem two_mul_Mexp_add (n : ℕ) : 2 * Mexp n + n = n * n := by
  rw [Mexp_eq_choose]
  exact two_mul_choose_two_add n

@[simp] theorem Mexp_zero : Mexp 0 = 0 := rfl

@[simp] theorem Mexp_one : Mexp 1 = 0 := rfl

/-! ### The exponent inequality

`(n-1) d ≤ C(j,2) + M n` for `1 ≤ d ≤ j ≤ n`, with equality exactly at `j = d = n`. -/

private theorem key_core {p j d : ℕ} (hdj : d ≤ j) (hjn : j ≤ p + 1) :
    2 * (p * d) + j + (p + 1) ≤ j * j + (p + 1) * (p + 1) := by
  have h1 : p * d ≤ p * j := Nat.mul_le_mul_left p hdj
  have h2 : 2 * (p * j) + j + (p + 1) ≤ j * j + (p + 1) * (p + 1) := by
    rcases (by omega : j ≤ p ∨ j = p + 1) with hc | hc
    · obtain ⟨q, rfl⟩ : ∃ q, p = j + q := ⟨p - j, by omega⟩
      have e1 : 2 * ((j + q) * j) + j + (j + q + 1)
          = 2 * (j * j) + 2 * (q * j) + 2 * j + q + 1 := by ring
      have e2 : j * j + (j + q + 1) * (j + q + 1)
          = 2 * (j * j) + 2 * (q * j) + 2 * j + q * q + 2 * q + 1 := by ring
      omega
    · subst hc
      have e1 : 2 * (p * (p + 1)) + (p + 1) + (p + 1) = 2 * (p * p) + 4 * p + 2 := by ring
      have e2 : (p + 1) * (p + 1) + (p + 1) * (p + 1) = 2 * (p * p) + 4 * p + 2 := by ring
      omega
  omega

/-- **The exponent inequality.** This is what makes `t^(Mexp n) · D_n · Q_n` integral
term by term. Sharp at `j = d = n`. -/
theorem key_exp {n j d : ℕ} (hd1 : 1 ≤ d) (hdj : d ≤ j) (hjn : j ≤ n) :
    (n - 1) * d ≤ j.choose 2 + Mexp n := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have hsub : p + 1 - 1 = p := by omega
  have hC : 2 * j.choose 2 + j = j * j := two_mul_choose_two_add j
  have hM : 2 * Mexp (p + 1) + (p + 1) = (p + 1) * (p + 1) := two_mul_Mexp_add (p + 1)
  have hk := key_core hdj hjn
  rw [hsub]
  omega

/-- The exponent bookkeeping inside `legQval`: `n i + d + (n-1) d = n j` when `d = j - i`. -/
private theorem qexp {n i j : ℕ} (hij : i < j) (hjn : j ≤ n) :
    n * i + (j - i) + (n - 1) * (j - i) = n * j := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  have e1 : i + d - i = d := by omega
  have e2 : p + 1 - 1 = p := by omega
  rw [e1, e2]
  ring

/-! ### The subring of real integers

Membership in `Zr` is exactly `∃ a : ℤ, (a : ℝ) = x`; using a `Subring` gives closure under
`Finset.sum` for free, which is what all the proofs below need. -/

/-- The image of `ℤ` in `ℝ`, as a subring. -/
noncomputable def Zr : Subring ℝ := (Int.castRingHom ℝ).range

theorem mem_Zr {x : ℝ} : x ∈ Zr ↔ ∃ a : ℤ, (a : ℝ) = x := RingHom.mem_range

theorem intCast_mem_Zr (a : ℤ) : ((a : ℝ)) ∈ Zr := mem_Zr.mpr ⟨a, rfl⟩

theorem exists_int_of_mem_Zr {x : ℝ} (h : x ∈ Zr) : ∃ a : ℤ, x = (a : ℝ) := by
  obtain ⟨a, ha⟩ := mem_Zr.mp h
  exact ⟨a, ha.symm⟩

/-! ### The integer behind `legCoef` -/

/-- `legCoef t n j = t^(C(j,2)) * coefZ t n j`, with `coefZ` an integer. -/
def coefZ (t : ℤ) (n j : ℕ) : ℤ := (-1) ^ j * qbin t 1 n j * qbin t 1 (n + j) n

theorem legCoef_eq_of_int {t : ℤ} (ht : 2 ≤ t) {n j : ℕ} (h : j ≤ n) :
    legCoef (t : ℝ) n j = (t : ℝ) ^ (j.choose 2) * (coefZ t n j : ℝ) := by
  have h1 : (1 : ℤ) < t := by linarith
  unfold legCoef coefZ
  rw [gauss_eq_qbin h1 h, gauss_eq_qbin h1 (Nat.le_add_right n j)]
  push_cast
  ring

/-! ### `P_n(t^n)` is an integer -/

theorem legVal_mem_Zr {t : ℤ} (ht : 2 ≤ t) (n : ℕ) : legVal (t : ℝ) n ∈ Zr := by
  rw [legVal_eq]
  refine Subring.sum_mem _ (fun j hj => ?_)
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [legCoef_eq_of_int ht hjn]
  refine mem_Zr.mpr ⟨t ^ (j.choose 2) * coefZ t n j, ?_⟩
  push_cast
  ring

/-- **`P_n(t^n)` is an integer for integer `t`.** No clearing factor is needed. -/
theorem legVal_isInt {t : ℤ} (ht : 2 ≤ t) (n : ℕ) :
    ∃ b : ℤ, legVal (t : ℝ) n = (b : ℝ) :=
  exists_int_of_mem_Zr (legVal_mem_Zr ht n)

/-! ### `D_n · headSum` is an integer -/

theorem Dr_mul_headSum_mem_Zr {t : ℤ} (ht : 2 ≤ t) (n : ℕ) :
    Dr (t : ℝ) n * headSum (t : ℝ) n ∈ Zr := by
  have htR : (1 : ℝ) < (t : ℝ) := by exact_mod_cast (by linarith : (1 : ℤ) < t)
  unfold headSum
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ (fun k hk => ?_)
  have hk' : k + 1 ≤ n := by have := Finset.mem_range.mp hk; omega
  obtain ⟨c, hc⟩ := Clearing.sub_one_dvd_Dz (t := t) (ℓ := k + 1) (by omega) hk'
  have hden : ((t : ℝ) ^ (k + 1) - 1) ≠ 0 := ne_of_gt (Clearing.sub_one_pos_real htR k)
  refine mem_Zr.mpr ⟨c, ?_⟩
  rw [Clearing.Dr_eq_Dz, hc]
  push_cast
  field_simp

/-- **`D_n · P_n(t^n) · headSum` is an integer.** -/
theorem Dr_mul_legVal_mul_headSum_isInt {t : ℤ} (ht : 2 ≤ t) (n : ℕ) :
    ∃ a : ℤ, Dr (t : ℝ) n * legVal (t : ℝ) n * headSum (t : ℝ) n = (a : ℝ) := by
  refine exists_int_of_mem_Zr ?_
  have hrw : Dr (t : ℝ) n * legVal (t : ℝ) n * headSum (t : ℝ) n
      = legVal (t : ℝ) n * (Dr (t : ℝ) n * headSum (t : ℝ) n) := by ring
  rw [hrw]
  exact Subring.mul_mem _ (legVal_mem_Zr ht n) (Dr_mul_headSum_mem_Zr ht n)

/-! ### `Q_n(t^n)` in a form with the `t`-powers displayed -/

/-- The single-term rewrite: `legGamma`'s negative `t`-power is pushed into the explicit
factor `(t^((n-1)d))⁻¹`, `d = j - i`. -/
private theorem qterm_rw {t : ℝ} (ht : 1 < t) {n i j : ℕ} (hij : i < j) (hjn : j ≤ n) :
    legGamma t n j * ((t ^ n) ^ i * (t ^ (j - i) / (t ^ (j - i) - 1)))
      = legCoef t n j * ((t ^ ((n - 1) * (j - i)))⁻¹ * (t ^ (j - i) - 1)⁻¹) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hd0 : j - i ≠ 0 := by omega
  have hdpos : (0 : ℝ) < t ^ (j - i) - 1 := by
    have : (1 : ℝ) < t ^ (j - i) := one_lt_pow₀ ht hd0
    linarith
  have hkey : t ^ (n * i) * t ^ (j - i) * t ^ ((n - 1) * (j - i)) = t ^ (n * j) := by
    rw [← pow_add, ← pow_add, qexp hij hjn]
  have hne1 : (t ^ (n * j)) ≠ 0 := ne_of_gt (pow_pos ht0 _)
  have hne2 : (t ^ ((n - 1) * (j - i))) ≠ 0 := ne_of_gt (pow_pos ht0 _)
  have hne3 : (t ^ (j - i) - 1) ≠ 0 := ne_of_gt hdpos
  unfold legGamma
  rw [← pow_mul, ← pow_mul]
  field_simp
  linear_combination legCoef t n j * hkey

/-- `Q_n(t^n)` with every `t`-power explicit. -/
theorem legQval_eq_flat {t : ℝ} (ht : 1 < t) (n : ℕ) :
    legQval t n = ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range j,
      legCoef t n j * ((t ^ ((n - 1) * (j - i)))⁻¹ * (t ^ (j - i) - 1)⁻¹) := by
  unfold legQval
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact qterm_rw ht (Finset.mem_range.mp hi) hjn

/-! ### The main integrality statements -/

theorem tM_Dr_mul_legQval_mem_Zr {t : ℤ} (ht : 2 ≤ t) (n : ℕ) :
    (t : ℝ) ^ Mexp n * Dr (t : ℝ) n * legQval (t : ℝ) n ∈ Zr := by
  have htZ : (1 : ℤ) < t := by linarith
  have htR : (1 : ℝ) < (t : ℝ) := by exact_mod_cast htZ
  have ht0 : (0 : ℝ) < (t : ℝ) := lt_trans zero_lt_one htR
  rw [legQval_eq_flat htR, Finset.mul_sum]
  refine Subring.sum_mem _ (fun j hj => ?_)
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ (fun i hi => ?_)
  have hij : i < j := Finset.mem_range.mp hi
  -- the working exponent `d = j - i`
  have hd1 : 1 ≤ j - i := by omega
  have hdj : j - i ≤ j := Nat.sub_le j i
  have hdn : j - i ≤ n := le_trans hdj hjn
  have hd0 : j - i ≠ 0 := by omega
  -- the surviving power of `t`
  obtain ⟨e, he⟩ : ∃ e, (n - 1) * (j - i) + e = j.choose 2 + Mexp n :=
    ⟨j.choose 2 + Mexp n - (n - 1) * (j - i), by have := key_exp hd1 hdj hjn; omega⟩
  -- the clearing of `t^d - 1`
  obtain ⟨c, hc⟩ := Clearing.sub_one_dvd_Dz (t := t) (ℓ := j - i) hd1 hdn
  have hdpos : (0 : ℝ) < (t : ℝ) ^ (j - i) - 1 := by
    have : (1 : ℝ) < (t : ℝ) ^ (j - i) := one_lt_pow₀ htR hd0
    linarith
  have hne2 : ((t : ℝ) ^ ((n - 1) * (j - i))) ≠ 0 := ne_of_gt (pow_pos ht0 _)
  have hne3 : ((t : ℝ) ^ (j - i) - 1) ≠ 0 := ne_of_gt hdpos
  have hpow : (t : ℝ) ^ (j.choose 2) * (t : ℝ) ^ (Mexp n)
      = (t : ℝ) ^ ((n - 1) * (j - i)) * (t : ℝ) ^ e := by
    rw [← pow_add, ← pow_add, he]
  refine mem_Zr.mpr ⟨coefZ t n j * t ^ e * c, ?_⟩
  rw [legCoef_eq_of_int ht hjn, Clearing.Dr_eq_Dz, hc]
  push_cast
  field_simp
  linear_combination (-((coefZ t n j : ℝ) * (c : ℝ))) * hpow

/-- **`t^(Mexp n) · D_n · Q_n(t^n)` is an integer.** -/
theorem tM_Dr_mul_legQval_isInt {t : ℤ} (ht : 2 ≤ t) (n : ℕ) :
    ∃ a : ℤ, (t : ℝ) ^ Mexp n * Dr (t : ℝ) n * legQval (t : ℝ) n = (a : ℝ) :=
  exists_int_of_mem_Zr (tM_Dr_mul_legQval_mem_Zr ht n)

theorem tM_Dr_mul_legVal_mem_Zr {t : ℤ} (ht : 2 ≤ t) (n : ℕ) :
    (t : ℝ) ^ Mexp n * Dr (t : ℝ) n * legVal (t : ℝ) n ∈ Zr := by
  have hDr : Dr (t : ℝ) n ∈ Zr := by
    rw [Clearing.Dr_eq_Dz]; exact intCast_mem_Zr _
  have hpow : ((t : ℝ)) ^ Mexp n ∈ Zr := by
    have : ((t : ℝ)) ^ Mexp n = (((t ^ Mexp n : ℤ) : ℝ)) := by push_cast; ring
    rw [this]; exact intCast_mem_Zr _
  exact Subring.mul_mem _ (Subring.mul_mem _ hpow hDr) (legVal_mem_Zr ht n)

/-- **`t^(Mexp n) · D_n · P_n(t^n)` is an integer.** -/
theorem tM_Dr_mul_legVal_isInt {t : ℤ} (ht : 2 ≤ t) (n : ℕ) :
    ∃ b : ℤ, (t : ℝ) ^ Mexp n * Dr (t : ℝ) n * legVal (t : ℝ) n = (b : ℝ) :=
  exists_int_of_mem_Zr (tM_Dr_mul_legVal_mem_Zr ht n)

theorem tM_Dr_mul_legVal_mul_headSum_mem_Zr {t : ℤ} (ht : 2 ≤ t) (n : ℕ) :
    (t : ℝ) ^ Mexp n * Dr (t : ℝ) n * legVal (t : ℝ) n * headSum (t : ℝ) n ∈ Zr := by
  have hpow : ((t : ℝ)) ^ Mexp n ∈ Zr := by
    have : ((t : ℝ)) ^ Mexp n = (((t ^ Mexp n : ℤ) : ℝ)) := by push_cast; ring
    rw [this]; exact intCast_mem_Zr _
  have hrw : (t : ℝ) ^ Mexp n * Dr (t : ℝ) n * legVal (t : ℝ) n * headSum (t : ℝ) n
      = (t : ℝ) ^ Mexp n * (legVal (t : ℝ) n * (Dr (t : ℝ) n * headSum (t : ℝ) n)) := by ring
  rw [hrw]
  exact Subring.mul_mem _ hpow
    (Subring.mul_mem _ (legVal_mem_Zr ht n) (Dr_mul_headSum_mem_Zr ht n))

/-- **`t^(Mexp n) · D_n · P_n(t^n) · headSum` is an integer.** -/
theorem tM_Dr_mul_legVal_mul_headSum_isInt {t : ℤ} (ht : 2 ≤ t) (n : ℕ) :
    ∃ a : ℤ, (t : ℝ) ^ Mexp n * Dr (t : ℝ) n * legVal (t : ℝ) n * headSum (t : ℝ) n = (a : ℝ) :=
  exists_int_of_mem_Zr (tM_Dr_mul_legVal_mul_headSum_mem_Zr ht n)

/-- **Integrality of `A_n`.** The combined form the assembly consumes:
`A_n = t^(Mexp n) · D_n · (Q_n(t^n) + P_n(t^n) · headSum) ∈ ℤ`. -/
theorem tM_Dr_mul_Aform_isInt {t : ℤ} (ht : 2 ≤ t) (n : ℕ) :
    ∃ a : ℤ, (t : ℝ) ^ Mexp n * Dr (t : ℝ) n *
      (legQval (t : ℝ) n + legVal (t : ℝ) n * headSum (t : ℝ) n) = (a : ℝ) := by
  refine exists_int_of_mem_Zr ?_
  have hrw : (t : ℝ) ^ Mexp n * Dr (t : ℝ) n *
      (legQval (t : ℝ) n + legVal (t : ℝ) n * headSum (t : ℝ) n)
      = (t : ℝ) ^ Mexp n * Dr (t : ℝ) n * legQval (t : ℝ) n
        + (t : ℝ) ^ Mexp n * Dr (t : ℝ) n * legVal (t : ℝ) n * headSum (t : ℝ) n := by ring
  rw [hrw]
  exact Subring.add_mem _ (tM_Dr_mul_legQval_mem_Zr ht n)
    (tM_Dr_mul_legVal_mul_headSum_mem_Zr ht n)

end QHarm

#print axioms QHarm.key_exp
#print axioms QHarm.legVal_isInt
#print axioms QHarm.Dr_mul_legVal_mul_headSum_isInt
#print axioms QHarm.tM_Dr_mul_legQval_isInt
#print axioms QHarm.tM_Dr_mul_legVal_isInt
#print axioms QHarm.tM_Dr_mul_legVal_mul_headSum_isInt
#print axioms QHarm.tM_Dr_mul_Aform_isInt
