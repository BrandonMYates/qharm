/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# QHarm/Clearing.lean — the crude clearing factor, integer track

## Consumes

Nothing. This file imports only Mathlib and depends on no other `QHarm` file. It is
completely `sorry`-free: there are no frontiers here.

## Main results

Per the internal build notes deviation **D1**, the integer track (`Q = 1`, `t : ℤ`, `t ≥ 2`)
does not need the sharp cyclotomic clearing factor `∏_{k≤n} Φ_k(P,Q)`, because the crude
product already clears everything and is small enough. This file owns that object.

* `QHarm.Dz` — `∏_{k=1}^{n} (t^k − 1)` over `ℤ`.
* `QHarm.Dr` — the same product over `ℝ`.
* `QHarm.Clearing.Dz_pos`, `QHarm.Clearing.Dr_pos` — positivity.
* `QHarm.Clearing.Dr_eq_Dz` — the two agree under `Int.cast`.
* `QHarm.Clearing.sub_one_dvd_Dz` — **the clearing property**: `(t^ℓ − 1) ∣ D_n` for
  every `1 ≤ ℓ ≤ n`. This is what lets the head sum `∑_{k<n} 1/(t^k − 1)` and the inner
  sums of Van Assche's (25) clear with a single factor.
* `QHarm.Clearing.Dr_sq_le` — **the size bound, squared form**:
  `(D_n)² ≤ t^{n(n+1)}`. ℕ-division-free; this is the form downstream code should
  consume.
* `QHarm.Clearing.Dr_le` — the same bound in divided form, `D_n ≤ t^{n(n+1)/2}`. The
  ℕ-division is exact here (`QHarm.Clearing.two_mul_gaussExp`), so nothing is lost.
* `QHarm.Clearing.gaussExp` / `two_mul_gaussExp` / `gaussExp_eq` — the exponent
  `∑_{k<n}(k+1) = n(n+1)/2`, isolated so that no consumer has to fight `Nat` division.

Numerically: `D_n^{1/n²} → t^{1/2}`, comfortably below the `t^{3/2}` supplied by
`|P_n(t^n)|`, which is the whole point of the crude route.

## What is NOT here

* The sharp clearing factor `∏_{k≤n} Φ_k(P,Q)` and its growth `D_n^{1/n²} → P^{3/π²}`
  (`QHarm/Cyclotomic.lean`, `QHarm/Mertens.lean`, `QHarm/Growth.lean`) — general track
  only.
* Anything about the linear forms `A n`, `B n`, `R n`, the q-Legendre polynomials, or
  the balance inequality itself (`QHarm/Forms.lean`, `QHarm/Main.lean`). This file makes
  no claim about irrationality; it is pure elementary algebra on a finite product.
* Integrality of the cleared linear forms — that is `QHarm/Forms.lean`'s job; this file
  only supplies the divisibility fact it needs.
-/

namespace QHarm

/-- Crude clearing factor `∏_{k=1}^{n} (t^k − 1)`, over `ℤ`. -/
def Dz (t : ℤ) (n : ℕ) : ℤ := ∏ k ∈ Finset.range n, (t ^ (k + 1) - 1)

/-- Real version of `QHarm.Dz`. -/
noncomputable def Dr (t : ℝ) (n : ℕ) : ℝ := ∏ k ∈ Finset.range n, (t ^ (k + 1) - 1)

namespace Clearing

/-! ### The Gauss exponent

`∑_{k<n} (k+1) = n(n+1)/2`. Kept as its own definition so that the size bound can be
stated without `Nat` division, and so that the divided form is a one-line corollary. -/

/-- The exponent appearing in the size bound: `∑_{k<n} (k+1)`. -/
def gaussExp (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, (k + 1)

@[simp] theorem gaussExp_zero : gaussExp 0 = 0 := by simp [gaussExp]

theorem gaussExp_succ (n : ℕ) : gaussExp (n + 1) = gaussExp n + (n + 1) := by
  simp [gaussExp, Finset.sum_range_succ]

/-- The Gauss identity, in the form that avoids `Nat` division entirely. -/
theorem two_mul_gaussExp (n : ℕ) : 2 * gaussExp n = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [gaussExp_succ, Nat.mul_add, ih]
    ring

/-- The `Nat` division in `n(n+1)/2` is exact. -/
theorem gaussExp_eq (n : ℕ) : gaussExp n = n * (n + 1) / 2 := by
  rw [← two_mul_gaussExp]
  omega

/-! ### Positivity -/

/-- Every factor of the clearing product is positive for an integer base `t ≥ 2`. -/
theorem sub_one_pos_int {t : ℤ} (ht : 2 ≤ t) (k : ℕ) : 0 < t ^ (k + 1) - 1 := by
  have h1 : (1 : ℤ) < t := by linarith
  have : (1 : ℤ) < t ^ (k + 1) := one_lt_pow₀ h1 (Nat.succ_ne_zero k)
  linarith

/-- Every factor of the clearing product is positive for a real base `t > 1`. -/
theorem sub_one_pos_real {t : ℝ} (ht : 1 < t) (k : ℕ) : 0 < t ^ (k + 1) - 1 := by
  have : (1 : ℝ) < t ^ (k + 1) := one_lt_pow₀ ht (Nat.succ_ne_zero k)
  linarith

theorem Dz_pos {t : ℤ} (ht : 2 ≤ t) (n : ℕ) : 0 < Dz t n := by
  unfold Dz
  exact Finset.prod_pos fun k _ => sub_one_pos_int ht k

theorem Dr_pos {t : ℝ} (ht : 1 < t) (n : ℕ) : 0 < Dr t n := by
  unfold Dr
  exact Finset.prod_pos fun k _ => sub_one_pos_real ht k

theorem Dr_nonneg {t : ℝ} (ht : 1 < t) (n : ℕ) : 0 ≤ Dr t n := (Dr_pos ht n).le

/-- The real and integer clearing factors agree under `Int.cast`. -/
theorem Dr_eq_Dz {t : ℤ} (n : ℕ) : Dr (t : ℝ) n = (Dz t n : ℝ) := by
  unfold Dr Dz
  push_cast
  ring

/-! ### The clearing property -/

/-- **The clearing property.** Every `t^ℓ − 1` with `1 ≤ ℓ ≤ n` divides `D n`. -/
theorem sub_one_dvd_Dz {t : ℤ} {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : ℓ ≤ n) :
    (t ^ ℓ - 1) ∣ Dz t n := by
  unfold Dz
  have hmem : (ℓ - 1) ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have h := Finset.dvd_prod_of_mem (fun k => t ^ (k + 1) - 1) hmem
  have he : ℓ - 1 + 1 = ℓ := Nat.sub_add_cancel hℓ
  simp only [he] at h
  exact h

/-- The real-side restatement of the clearing property, for consumers that work over `ℝ`
after `Dr_eq_Dz`. -/
theorem sub_one_dvd_Dz' {t : ℤ} {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : ℓ ≤ n) :
    ∃ c : ℤ, Dz t n = (t ^ ℓ - 1) * c := sub_one_dvd_Dz hℓ hn

/-! ### The size bound -/

/-- The clearing product is bounded termwise by `∏_{k<n} t^{k+1}`, i.e. by
`t ^ gaussExp n`. -/
theorem Dr_le_gaussExp {t : ℝ} (ht : 1 < t) (n : ℕ) : Dr t n ≤ t ^ gaussExp n := by
  unfold Dr
  calc ∏ k ∈ Finset.range n, (t ^ (k + 1) - 1)
      ≤ ∏ k ∈ Finset.range n, t ^ (k + 1) := by
        refine Finset.prod_le_prod (fun k _ => ?_) (fun k _ => ?_)
        · exact (sub_one_pos_real ht k).le
        · linarith
    _ = t ^ gaussExp n := by
        rw [Finset.prod_pow_eq_pow_sum]
        rfl

/-- **The size bound, squared form** — `(D_n)² ≤ t^{n(n+1)}`. No `Nat` division; this is
the form downstream code should consume. -/
theorem Dr_sq_le {t : ℝ} (ht : 1 < t) (n : ℕ) : (Dr t n) ^ 2 ≤ t ^ (n * (n + 1)) := by
  have h1 : Dr t n ≤ t ^ gaussExp n := Dr_le_gaussExp ht n
  calc (Dr t n) ^ 2 ≤ (t ^ gaussExp n) ^ 2 := pow_le_pow_left₀ (Dr_nonneg ht n) h1 2
    _ = t ^ (2 * gaussExp n) := by rw [← pow_mul, Nat.mul_comm]
    _ = t ^ (n * (n + 1)) := by rw [two_mul_gaussExp]

/-- **The size bound.** `D_n ≤ t^{n(n+1)/2}` — the whole point of the crude route. The
`Nat` division is exact (`gaussExp_eq`). -/
theorem Dr_le {t : ℝ} (ht : 1 < t) (n : ℕ) : Dr t n ≤ t ^ (n * (n + 1) / 2) := by
  rw [← gaussExp_eq]
  exact Dr_le_gaussExp ht n

/-- Division-free restatement: any `e` with `2 * e = n * (n+1)` works as the exponent. -/
theorem Dr_le_of_two_mul {t : ℝ} (ht : 1 < t) {n e : ℕ} (he : 2 * e = n * (n + 1)) :
    Dr t n ≤ t ^ e := by
  have : e = gaussExp n := by
    have := two_mul_gaussExp n
    omega
  rw [this]
  exact Dr_le_gaussExp ht n

/-- The integer-side size bound, obtained from `Dr_le` through `Dr_eq_Dz`. -/
theorem Dz_le {t : ℤ} (ht : 2 ≤ t) (n : ℕ) : Dz t n ≤ t ^ (n * (n + 1) / 2) := by
  have h1 : (1 : ℝ) < (t : ℝ) := by exact_mod_cast (by linarith : (1 : ℤ) < t)
  have h := Dr_le h1 n
  rw [Dr_eq_Dz] at h
  exact_mod_cast h

end Clearing

end QHarm

#print axioms QHarm.Clearing.Dz_pos
#print axioms QHarm.Clearing.sub_one_dvd_Dz
#print axioms QHarm.Clearing.Dr_sq_le
#print axioms QHarm.Clearing.Dr_le
