import Mathlib

/-!
# Gaussian (`q`-)binomial coefficients

**Consumes.** Nothing from `QHarm`; Mathlib only. This file is a root of the `QHarm`
dependency graph, so every statement below is proved outright.

**Main results.**

* `QHarm.qbin` — the two-variable *homogeneous* Gaussian binomial over `ℤ`, defined by the
  homogeneous `q`-Pascal recurrence

  `[n+1, k+1] = Q^(k+1) * [n, k+1] + P^(n-k) * [n, k]`,

  so that **integrality is definitional** rather than a theorem about a quotient of
  integers.  `qbin_zero_right`, `qbin_zero_succ`, `qbin_succ_succ`, `qbin_eq_zero_of_lt`
  and `qbin_self` are the basic structural facts.
* `qbin_mul_prod` — the product (Gauss) formula in **division-free form**:
  `qbin P Q n k * ∏_{j<k} (P^(j+1) - Q^(j+1)) = ∏_{j<k} (P^(n-k+j+1) - Q^(n-k+j+1))`.
  This *is* the integrality statement; `qbin_one_mul_prod` is its `Q = 1` specialisation.
* `QHarm.gauss` — the real one-variable Gaussian binomial
  `∏_{j<k} (t^(n-k+j+1) - 1)/(t^(j+1) - 1)`, with `gauss_pos`, and `gauss_eq_qbin`
  identifying it with the integer object at integer `t` and `Q = 1`.
* `pow_le_gauss` and `gauss_le_const_mul_pow` — the two-sided size estimate
  `t^(k(n-k)) ≤ gauss t n k ≤ gaussConst t * t^(k(n-k))` for `t > 1`, where
  `gaussConst t = exp (t / (t-1)^2)` depends on **neither `n` nor `k`**.  That uniformity
  is the point: it is what makes the dominant-term separation downstream work.

**What is NOT here.**  The `q`-Pochhammer factors, the little `q`-Legendre polynomials
(`QHarm/Legendre.lean`), the clearing factors `Dcrude` (`QHarm/Clearing.lean`), and the
degree maximisation (`QHarm/Degree.lean`).  Nothing in this file knows about `S t`,
orthogonality, or the Padé forms.
-/

set_option linter.unusedVariables false

namespace QHarm

open Finset

/-! ## The integer two-variable homogeneous Gaussian binomial -/

/-- Two-variable homogeneous Gaussian binomial over `ℤ`, defined by the homogeneous
q-Pascal recurrence so that integrality is definitional. -/
def qbin (P Q : ℤ) : ℕ → ℕ → ℤ
  | _, 0 => 1
  | 0, (_ + 1) => 0
  | (n + 1), (k + 1) => Q ^ (k + 1) * qbin P Q n (k + 1) + P ^ (n - k) * qbin P Q n k

@[simp] theorem qbin_zero_right (P Q : ℤ) (n : ℕ) : qbin P Q n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem qbin_zero_succ (P Q : ℤ) (k : ℕ) : qbin P Q 0 (k + 1) = 0 := rfl

theorem qbin_succ_succ (P Q : ℤ) (n k : ℕ) :
    qbin P Q (n + 1) (k + 1) = Q ^ (k + 1) * qbin P Q n (k + 1) + P ^ (n - k) * qbin P Q n k :=
  rfl

private theorem qbin_eq_zero_aux (P Q : ℤ) : ∀ n k : ℕ, n < k → qbin P Q n k = 0 := by
  intro n
  induction n with
  | zero =>
      intro k hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact qbin_zero_succ P Q k'
  | succ n ih =>
      intro k hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [qbin_succ_succ, ih (k' + 1) (by omega), ih k' (by omega)]
      ring

theorem qbin_eq_zero_of_lt (P Q : ℤ) {n k : ℕ} (h : n < k) : qbin P Q n k = 0 :=
  qbin_eq_zero_aux P Q n k h

@[simp] theorem qbin_self (P Q : ℤ) (n : ℕ) : qbin P Q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [qbin_succ_succ, qbin_eq_zero_of_lt P Q (Nat.lt_succ_self n), ih, Nat.sub_self]
      ring

/-! ## The product formula -/

/-- The product formula in the `n = m + k` parametrisation, where ℕ-subtraction has been
eliminated. -/
theorem qbin_mul_prod_aux (P Q : ℤ) (m k : ℕ) :
    qbin P Q (m + k) k * ∏ j ∈ Finset.range k, (P ^ (j + 1) - Q ^ (j + 1))
      = ∏ j ∈ Finset.range k, (P ^ (m + j + 1) - Q ^ (m + j + 1)) := by
  induction m generalizing k with
  | zero => simp
  | succ m ihm =>
      induction k with
      | zero => simp
      | succ k ihk =>
          -- unfold the two products at their top factor
          rw [Finset.prod_range_succ (fun j => P ^ (j + 1) - Q ^ (j + 1)) k,
              Finset.prod_range_succ (fun j => P ^ (m + 1 + j + 1) - Q ^ (m + 1 + j + 1)) k]
          -- unfold the q-Pascal recurrence
          rw [show m + 1 + (k + 1) = (m + k + 1) + 1 from by omega, qbin_succ_succ,
              show m + k + 1 - k = m + 1 from by omega,
              show qbin P Q (m + k + 1) (k + 1) = qbin P Q (m + (k + 1)) (k + 1) from by
                rw [show m + k + 1 = m + (k + 1) from by omega],
              show qbin P Q (m + k + 1) k = qbin P Q (m + 1 + k) k from by
                rw [show m + k + 1 = m + 1 + k from by omega]]
          -- the two induction hypotheses
          have hU := ihm (k + 1)
          rw [Finset.prod_range_succ (fun j => P ^ (j + 1) - Q ^ (j + 1)) k] at hU
          -- index shift:  ∏_{j<k+1} f(m+j) = f(m) * ∏_{j<k} f(m+1+j)
          have hshift :
              ∏ j ∈ Finset.range (k + 1), (P ^ (m + j + 1) - Q ^ (m + j + 1))
                = (P ^ (m + 1) - Q ^ (m + 1)) *
                    ∏ j ∈ Finset.range k, (P ^ (m + 1 + j + 1) - Q ^ (m + 1 + j + 1)) := by
            rw [Finset.prod_range_succ' (fun j => P ^ (m + j + 1) - Q ^ (m + j + 1)) k]
            simp only [show ∀ j : ℕ, m + (j + 1) + 1 = m + 1 + j + 1 from fun j => by omega,
              Nat.add_zero]
            ring
          rw [hshift] at hU
          linear_combination
            Q ^ (k + 1) * hU + P ^ (m + 1) * (P ^ (k + 1) - Q ^ (k + 1)) * ihk

/-- **The product formula, in division-free form.** This is the integrality statement. -/
theorem qbin_mul_prod (P Q : ℤ) {n k : ℕ} (h : k ≤ n) :
    qbin P Q n k * ∏ j ∈ Finset.range k, (P ^ (j + 1) - Q ^ (j + 1))
      = ∏ j ∈ Finset.range k, (P ^ (n - k + j + 1) - Q ^ (n - k + j + 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, Nat.add_comm k m]
  exact qbin_mul_prod_aux P Q m k

/-- Specialisation `Q = 1`: the one-variable integer Gaussian binomial. -/
theorem qbin_one_mul_prod (P : ℤ) {n k : ℕ} (h : k ≤ n) :
    qbin P 1 n k * ∏ j ∈ Finset.range k, (P ^ (j + 1) - 1)
      = ∏ j ∈ Finset.range k, (P ^ (n - k + j + 1) - 1) := by
  have := qbin_mul_prod P 1 h
  simpa using this

/-! ## The real one-variable Gaussian binomial -/

/-- Real one-variable Gaussian binomial. -/
noncomputable def gauss (t : ℝ) (n k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (t ^ (n - k + j + 1) - 1) / (t ^ (j + 1) - 1)

private theorem gauss_add (t : ℝ) (m k : ℕ) :
    gauss t (m + k) k = ∏ j ∈ Finset.range k, (t ^ (m + j + 1) - 1) / (t ^ (j + 1) - 1) := by
  unfold gauss
  simp only [Nat.add_sub_cancel]

private theorem one_lt_pow_of_one_lt {t : ℝ} (ht : 1 < t) (j : ℕ) : 1 < t ^ (j + 1) :=
  one_lt_pow₀ ht (Nat.succ_ne_zero j)

private theorem den_pos {t : ℝ} (ht : 1 < t) (j : ℕ) : 0 < t ^ (j + 1) - 1 := by
  have := one_lt_pow_of_one_lt ht j
  linarith

theorem gauss_pos {t : ℝ} (ht : 1 < t) {n k : ℕ} (h : k ≤ n) : 0 < gauss t n k := by
  unfold gauss
  refine Finset.prod_pos ?_
  intro j _
  exact div_pos (by have := den_pos ht (n - k + j); linarith [den_pos ht (n - k + j)])
    (den_pos ht j)

/-- `gauss` at `t` agrees with the integer object at `Q = 1`. -/
theorem gauss_eq_qbin {t : ℤ} (ht : 1 < t) {n k : ℕ} (h : k ≤ n) :
    gauss (t : ℝ) n k = (qbin t 1 n k : ℝ) := by
  have htR : (1 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hden : (∏ j ∈ Finset.range k, ((t : ℝ) ^ (j + 1) - 1)) ≠ 0 := by
    refine ne_of_gt (Finset.prod_pos ?_)
    intro j _
    exact den_pos htR j
  have hint := qbin_one_mul_prod t h
  have hcast : (qbin t 1 n k : ℝ) * ∏ j ∈ Finset.range k, ((t : ℝ) ^ (j + 1) - 1)
      = ∏ j ∈ Finset.range k, ((t : ℝ) ^ (n - k + j + 1) - 1) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hint
  unfold gauss
  rw [Finset.prod_div_distrib, div_eq_iff hden, hcast]

/-! ## The two-sided size estimate -/

private theorem pow_le_gauss_aux {t : ℝ} (ht : 1 < t) (m k : ℕ) :
    t ^ (k * m) ≤ ∏ j ∈ Finset.range k, (t ^ (m + j + 1) - 1) / (t ^ (j + 1) - 1) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hm : (1 : ℝ) ≤ t ^ m := one_le_pow₀ ht.le
  have hstep : ∀ j ∈ Finset.range k,
      t ^ m ≤ (t ^ (m + j + 1) - 1) / (t ^ (j + 1) - 1) := by
    intro j _
    rw [le_div_iff₀ (den_pos ht j)]
    have hexp : t ^ m * (t ^ (j + 1) - 1) = t ^ (m + j + 1) - t ^ m := by ring
    rw [hexp]
    linarith
  calc t ^ (k * m) = ∏ _j ∈ Finset.range k, t ^ m := by
        rw [Finset.prod_const, Finset.card_range, ← pow_mul, Nat.mul_comm]
    _ ≤ ∏ j ∈ Finset.range k, (t ^ (m + j + 1) - 1) / (t ^ (j + 1) - 1) :=
        Finset.prod_le_prod (fun j _ => le_trans zero_le_one hm) hstep

/-- **Lower bound.** -/
theorem pow_le_gauss {t : ℝ} (ht : 1 < t) {n k : ℕ} (h : k ≤ n) :
    t ^ (k * (n - k)) ≤ gauss t n k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, Nat.add_comm k m, gauss_add]
  exact pow_le_gauss_aux ht m k

/-- The universal constant controlling the upper bound. -/
noncomputable def gaussConst (t : ℝ) : ℝ := Real.exp (t / (t - 1) ^ 2)

theorem one_le_gaussConst {t : ℝ} (ht : 1 < t) : 1 ≤ gaussConst t := by
  refine Real.one_le_exp ?_
  exact div_nonneg (by linarith) (sq_nonneg _)

/-- Geometric-series bound, proved directly to avoid a `tsum`. -/
private theorem geom_sum_le_inv {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (k : ℕ) :
    ∑ j ∈ Finset.range k, r ^ j ≤ 1 / (1 - r) := by
  have hpos : (0 : ℝ) < 1 - r := by linarith
  induction k with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
  | succ k ih =>
      rw [Finset.sum_range_succ' (fun j => r ^ j) k]
      have hsplit : ∑ j ∈ Finset.range k, r ^ (j + 1) = r * ∑ j ∈ Finset.range k, r ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      have h2 : r * ∑ j ∈ Finset.range k, r ^ j ≤ r * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left ih h0
      have h3 : r * (1 / (1 - r)) + 1 = 1 / (1 - r) := by
        field_simp
        ring
      rw [hsplit]
      simp only [pow_zero]
      linarith

/-- The tail sum `∑_{j<k} 1/(t^(j+1) - 1)` is bounded by `t/(t-1)^2`, uniformly in `k`. -/
private theorem sum_inv_pow_sub_one_le {t : ℝ} (ht : 1 < t) (k : ℕ) :
    ∑ j ∈ Finset.range k, 1 / (t ^ (j + 1) - 1) ≤ t / (t - 1) ^ 2 := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have ht1 : (0 : ℝ) < t - 1 := by linarith
  have hstep : ∀ j ∈ Finset.range k,
      1 / (t ^ (j + 1) - 1) ≤ (1 / (t - 1)) * (1 / t) ^ j := by
    intro j _
    have hpj : (1 : ℝ) ≤ t ^ j := one_le_pow₀ ht.le
    have hpj0 : (0 : ℝ) < t ^ j := lt_of_lt_of_le zero_lt_one hpj
    have hlow : (0 : ℝ) < t ^ j * (t - 1) := mul_pos hpj0 ht1
    have hle : t ^ j * (t - 1) ≤ t ^ (j + 1) - 1 := by
      have : t ^ j * (t - 1) = t ^ (j + 1) - t ^ j := by ring
      rw [this]; linarith
    have := one_div_le_one_div_of_le hlow hle
    refine le_trans this (le_of_eq ?_)
    rw [div_pow, one_pow]
    field_simp
  have hsum : ∑ j ∈ Finset.range k, 1 / (t ^ (j + 1) - 1)
      ≤ ∑ j ∈ Finset.range k, (1 / (t - 1)) * (1 / t) ^ j :=
    Finset.sum_le_sum hstep
  have hgeom : ∑ j ∈ Finset.range k, (1 / t) ^ j ≤ 1 / (1 - 1 / t) := by
    refine geom_sum_le_inv (by positivity) ?_ k
    rw [div_lt_one ht0]; linarith
  have hrw : ∑ j ∈ Finset.range k, (1 / (t - 1)) * (1 / t) ^ j
      = (1 / (t - 1)) * ∑ j ∈ Finset.range k, (1 / t) ^ j := by
    rw [Finset.mul_sum]
  have hfin : (1 / (t - 1)) * (1 / (1 - 1 / t)) = t / (t - 1) ^ 2 := by
    have h1 : (1 : ℝ) - 1 / t = (t - 1) / t := by field_simp
    rw [h1]
    field_simp
  calc ∑ j ∈ Finset.range k, 1 / (t ^ (j + 1) - 1)
      ≤ (1 / (t - 1)) * ∑ j ∈ Finset.range k, (1 / t) ^ j := by rw [← hrw]; exact hsum
    _ ≤ (1 / (t - 1)) * (1 / (1 - 1 / t)) := by
        refine mul_le_mul_of_nonneg_left hgeom ?_
        positivity
    _ = t / (t - 1) ^ 2 := hfin

private theorem gauss_le_const_mul_pow_aux {t : ℝ} (ht : 1 < t) (m k : ℕ) :
    (∏ j ∈ Finset.range k, (t ^ (m + j + 1) - 1) / (t ^ (j + 1) - 1))
      ≤ gaussConst t * t ^ (k * m) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hmpos : (0 : ℝ) < t ^ m := pow_pos ht0 m
  -- factorwise bound
  have hstep : ∀ j ∈ Finset.range k,
      (t ^ (m + j + 1) - 1) / (t ^ (j + 1) - 1)
        ≤ t ^ m * Real.exp (1 / (t ^ (j + 1) - 1)) := by
    intro j _
    have hd : (0 : ℝ) < t ^ (j + 1) - 1 := den_pos ht j
    have hexp : 1 + 1 / (t ^ (j + 1) - 1) ≤ Real.exp (1 / (t ^ (j + 1) - 1)) := by
      have := Real.add_one_le_exp (1 / (t ^ (j + 1) - 1))
      linarith
    have h1 : (1 + 1 / (t ^ (j + 1) - 1)) * (t ^ (j + 1) - 1) = t ^ (j + 1) := by
      field_simp
      ring
    have key : t ^ (m + j + 1)
        ≤ t ^ m * Real.exp (1 / (t ^ (j + 1) - 1)) * (t ^ (j + 1) - 1) := by
      calc t ^ (m + j + 1) = t ^ m * ((1 + 1 / (t ^ (j + 1) - 1)) * (t ^ (j + 1) - 1)) := by
            rw [h1]; ring
        _ ≤ t ^ m * (Real.exp (1 / (t ^ (j + 1) - 1)) * (t ^ (j + 1) - 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ hmpos.le
            exact mul_le_mul_of_nonneg_right hexp hd.le
        _ = t ^ m * Real.exp (1 / (t ^ (j + 1) - 1)) * (t ^ (j + 1) - 1) := by ring
    rw [div_le_iff₀ hd]
    linarith
  have hnn : ∀ j ∈ Finset.range k,
      (0 : ℝ) ≤ (t ^ (m + j + 1) - 1) / (t ^ (j + 1) - 1) := by
    intro j _
    exact le_of_lt (div_pos (by linarith [den_pos ht (m + j)]) (den_pos ht j))
  have hprod := Finset.prod_le_prod hnn hstep
  -- evaluate the majorant
  have hmaj : (∏ j ∈ Finset.range k, t ^ m * Real.exp (1 / (t ^ (j + 1) - 1)))
      = t ^ (k * m) * Real.exp (∑ j ∈ Finset.range k, 1 / (t ^ (j + 1) - 1)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul,
      Nat.mul_comm m k, Real.exp_sum]
  rw [hmaj] at hprod
  refine le_trans hprod ?_
  have hexpbd : Real.exp (∑ j ∈ Finset.range k, 1 / (t ^ (j + 1) - 1)) ≤ gaussConst t := by
    unfold gaussConst
    exact Real.exp_le_exp.mpr (sum_inv_pow_sub_one_le ht k)
  calc t ^ (k * m) * Real.exp (∑ j ∈ Finset.range k, 1 / (t ^ (j + 1) - 1))
      ≤ t ^ (k * m) * gaussConst t := by
        refine mul_le_mul_of_nonneg_left hexpbd ?_
        positivity
    _ = gaussConst t * t ^ (k * m) := by ring

/-- **Upper bound.** Note the constant does not depend on `n` or `k` — that is the whole
point, and it is what makes the dominant-term separation downstream work. -/
theorem gauss_le_const_mul_pow {t : ℝ} (ht : 1 < t) {n k : ℕ} (h : k ≤ n) :
    gauss t n k ≤ gaussConst t * t ^ (k * (n - k)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, Nat.add_comm k m, gauss_add]
  exact gauss_le_const_mul_pow_aux ht m k

end QHarm

#print axioms QHarm.qbin_mul_prod
#print axioms QHarm.pow_le_gauss
#print axioms QHarm.gauss_le_const_mul_pow
