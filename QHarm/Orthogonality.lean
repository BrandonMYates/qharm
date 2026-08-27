/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QHarm.Legendre

/-!
# `QHarm/Orthogonality.lean` — the vanishing half of little q-Legendre orthogonality

## Consumes

* `QHarm/Legendre.lean` — `legCoef`, `legG`, `legGamma`;
* `QHarm/QBinom.lean` — `gauss` and its definition as a product of `(t^a - 1)` quotients.

## Method (design decision D3)

No `₃φ₂`, no q-Saalschütz.  Fix `t > 1`, put `q = t⁻¹` and take the `n+1` distinct nodes
`y j = q^j`, `j = 0..n`.  Lagrange interpolation of the degree-`n` polynomial
`N(y) = ∏_{r=1}^{n} (y - t^r)` at those nodes, divided through by `∏_j (z - y j)`, is the
Cauchy partial-fraction identity `cauchy_lagrange`.  The Lagrange coefficient
`N(y j) / ∏_{i ≠ j} (y j - y i)` is the little q-Legendre coefficient up to the
**`j`-independent** scalar `(-1)^n t^{n(n+1)/2}` (`lagrange_coef`); that cancellation is the
whole content of the file and it is a closed-form product computation, carried out through the
"t-factorial" `Rfac t m = ∏_{s<m} (t^{s+1} - 1)`.

## Main results

* `cauchy_lagrange` — the Lagrange/partial-fraction identity over an arbitrary field.
* `orth_moment` — for **every** `m`, the closed form
  `(-1)^n t^{C(n+1,2)} · ∑_{j≤n} γ_{n,j} t^j / (t^{m+j+1} - 1)
      = ∏_{r<n}(t^{m+1} - t^{r+1}) / ∏_{j≤n}(t^{m+1} - q^j)`.
* `orth_finset` — the `m < n` case: the sum vanishes (the numerator has a zero factor).
* `moment_n` — the `m = n` case: the sum is the explicit nonzero quotient above.
* `orth_tsum`, `orth_tsum_lt` — the series forms consumed by `QHarm/Pade.lean` /
  `QHarm/Forms.lean`.
* `moment_tsum` — the general-`m` series moment `L(x^m P_n)`.
* `norm_sq_eq` — `h_n = γ_{n,n} · L(x^n P_n)`, the reduction of the squared norm.
* `norm_sq_value` — the squared norm **exactly**: `h_n = t^{n+1} / (t^{2n+1} - 1)`
  (Van Assche's `q^n/(1 - q^{2n+1})`).  Delivered as an identity, not a bound.
* auxiliary but reusable: `Rfac` (the t-factorial) with `Rfac_pos`, `Rfac_split`,
  `gauss_mul_Rfac` (the division-free product formula `[n,j] [j]! [n-j]! = [n]!`),
  `gauss_diag`, `legG_lattice`, `summable_lattice`.

## What is NOT here

* the Padé identity (22) — `QHarm/Forms.lean`;
* the sum-of-squares form (34) — `QHarm/Forms.lean`;
* integrality of `D_n · legVal` — `QHarm/Integrality.lean`;
* any size bound on `legVal` or on the remainder — `QHarm/LegendreBounds.lean`
  (the squared norm `h_n` **is** here, and exactly: see `norm_sq_value`);
* zero-localisation of `legG` in `[0,1]` — deleted from the DAG by deviation D2.
-/

namespace QHarm

/-! ## Triangular-number bookkeeping

`Nat.choose k 2 = k(k-1)/2` is used for every triangular exponent, so that no ℕ-division ever
appears.  The one identity that matters is `tri_key`, the exponent cancellation that makes the
Lagrange coefficient proportional to `legGamma` with a `j`-independent constant.
-/

private theorem choose_two_succ (k : ℕ) : (k + 1).choose 2 = k + k.choose 2 := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right]

private theorem two_choose_two_add (j : ℕ) : 2 * j.choose 2 + j = j * j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h : 2 * (j + j.choose 2) + (j + 1) = (2 * j.choose 2 + j) + (2 * j + 1) := by ring
      rw [choose_two_succ, h, ih]
      ring

/-- `∑_{u<m} (u+1) = m(m+1)/2`. -/
private theorem sum_range_succ_choose (m : ℕ) :
    ∑ u ∈ Finset.range m, (u + 1) = (m + 1).choose 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, choose_two_succ (m + 1)]
      omega

/-- **The exponent cancellation.**  `(n-j)(n-j+1)/2 + nj = n(n+1)/2 + j(j-1)/2`.  The right side
is `j`-dependent only through `j.choose 2`, which is exactly the `j`-dependence carried by
`legCoef`; the left side is what the Lagrange denominator produces. -/
private theorem tri_key {n j : ℕ} (hj : j ≤ n) :
    (n - j + 1).choose 2 + n * j = (n + 1).choose 2 + j.choose 2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hd : j + d - j = d := by omega
  rw [hd]
  refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) ?_
  have h1 := two_choose_two_add (d + 1)
  have h2 := two_choose_two_add (j + d + 1)
  have h3 := two_choose_two_add j
  nlinarith [h1, h2, h3]

/-! ## Step 1 — the Cauchy/Lagrange partial-fraction identity

Over any field: if `N` has degree `< #s` and `z` avoids the nodes, then the partial-fraction
expansion of `N(z) / ∏_j (z - y j)` has the Lagrange coefficients as residues. -/

/-- **Cauchy's partial-fraction identity.**  Proved by evaluating Mathlib's
`Lagrange.eq_interpolate` (in the `Lagrange.interpolate_eq_sum` shape) at `z` and dividing by
the nodal polynomial `∏_{j ∈ s} (z - y j)`. -/
theorem cauchy_lagrange {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (y : ι → F) (hinj : Set.InjOn y s)
    (N : Polynomial F) (hdeg : N.degree < s.card)
    (z : F) (hz : ∀ j ∈ s, z ≠ y j) :
    ∑ j ∈ s, N.eval (y j) / ((∏ i ∈ s.erase j, (y j - y i)) * (z - y j))
      = N.eval z / ∏ j ∈ s, (z - y j) := by
  have hzne : ∀ j ∈ s, z - y j ≠ 0 := fun j hj => sub_ne_zero_of_ne (hz j hj)
  have hden : (∏ j ∈ s, (z - y j)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hzne
  rw [eq_div_iff hden, Finset.sum_mul]
  have h := congrArg (Polynomial.eval z) (Lagrange.eq_interpolate hinj hdeg)
  rw [Lagrange.interpolate_eq_sum, Polynomial.eval_finsetSum] at h
  rw [h]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hPne : (∏ k ∈ s.erase i, (y i - y k)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
    obtain ⟨hki, hks⟩ := Finset.mem_erase.mp hk
    exact sub_ne_zero_of_ne fun hEq =>
      hki (hinj (Finset.mem_coe.mpr hks) (Finset.mem_coe.mpr hi) hEq.symm)
  have hsplit : (∏ k ∈ s, (z - y k)) = (z - y i) * ∏ k ∈ s.erase i, (z - y k) :=
    (Finset.mul_prod_erase s _ hi).symm
  have hzi : z - y i ≠ 0 := hzne i hi
  rw [hsplit]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X]
  field_simp

/-! ## Step 2 — the `t`-factorial and the division-free Gaussian binomial -/

/-- The "t-factorial" `∏_{s<m} (t^{s+1} - 1)`.  Every product occurring in the Lagrange
coefficient is a ratio of these times a power of `t`. -/
noncomputable def Rfac (t : ℝ) (m : ℕ) : ℝ := ∏ s ∈ Finset.range m, (t ^ (s + 1) - 1)

@[simp] theorem Rfac_zero (t : ℝ) : Rfac t 0 = 1 := by simp [Rfac]

theorem Rfac_pos {t : ℝ} (ht : 1 < t) (m : ℕ) : 0 < Rfac t m := by
  refine Finset.prod_pos fun s _ => ?_
  have : (1 : ℝ) < t ^ (s + 1) := one_lt_pow₀ ht (Nat.succ_ne_zero s)
  linarith

theorem Rfac_ne_zero {t : ℝ} (ht : 1 < t) (m : ℕ) : Rfac t m ≠ 0 := (Rfac_pos ht m).ne'

theorem Rfac_split (t : ℝ) (a b : ℕ) :
    Rfac t (a + b) = Rfac t a * ∏ i ∈ Finset.range b, (t ^ (a + i + 1) - 1) := by
  simp only [Rfac]
  rw [Finset.prod_range_add]

/-- **The division-free product formula for `gauss`.**  `[n,j]_t · [j]_t! · [n-j]_t! = [n]_t!`. -/
theorem gauss_mul_Rfac {t : ℝ} (ht : 1 < t) {n j : ℕ} (h : j ≤ n) :
    gauss t n j * Rfac t j * Rfac t (n - j) = Rfac t n := by
  have hd : ∀ i : ℕ, t ^ (i + 1) - 1 ≠ 0 := by
    intro i
    have : (1 : ℝ) < t ^ (i + 1) := one_lt_pow₀ ht (Nat.succ_ne_zero i)
    linarith
  have h1 : gauss t n j * Rfac t j = ∏ i ∈ Finset.range j, (t ^ (n - j + i + 1) - 1) := by
    simp only [gauss, Rfac]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => div_mul_cancel₀ _ (hd i)
  rw [h1]
  have h2 := Rfac_split t (n - j) j
  rw [Nat.sub_add_cancel h] at h2
  rw [h2]
  ring

/-- The product of the two Gaussian binomials appearing in `legCoef`, division-free. -/
private theorem gauss_prod {t : ℝ} (ht : 1 < t) {n j : ℕ} (hj : j ≤ n) :
    gauss t n j * gauss t (n + j) n * (Rfac t j * Rfac t j * Rfac t (n - j))
      = Rfac t (n + j) := by
  have h1 := gauss_mul_Rfac ht hj
  have h2 := gauss_mul_Rfac ht (Nat.le_add_right n j)
  rw [show n + j - n = j from by omega] at h2
  linear_combination (gauss t (n + j) n * Rfac t j) * h1 + h2

/-! ## Step 3 — the two node products -/

/-- `N(q^j) = ∏_{r=1}^{n} (q^j - t^r)`, cleared of negative powers. -/
private theorem Nprod_eval {t : ℝ} (ht : 1 < t) (n j : ℕ) :
    Rfac t j * (t ^ (n * j) * ∏ r ∈ Finset.range n, ((t⁻¹) ^ j - t ^ (r + 1)))
      = (-1) ^ n * Rfac t (n + j) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt ht0
  have hfac : ∀ r ∈ Finset.range n,
      ((t⁻¹) ^ j - t ^ (r + 1)) = (-(t⁻¹) ^ j) * (t ^ (j + r + 1) - 1) := by
    intro r _
    have hpow : t ^ (j + r + 1) = t ^ j * t ^ (r + 1) := by
      rw [show j + r + 1 = j + (r + 1) from by omega, pow_add]
    have hjt : (t⁻¹) ^ j * t ^ j = 1 := by rw [← mul_pow, inv_mul_cancel₀ htne, one_pow]
    rw [hpow]
    linear_combination (t ^ (r + 1)) * hjt
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range, neg_pow]
  have hunit : t ^ (n * j) * ((t⁻¹) ^ j) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm j n, ← mul_pow, mul_inv_cancel₀ htne, one_pow]
  have hsplit := Rfac_split t j n
  rw [Nat.add_comm n j]
  linear_combination ((-1 : ℝ) ^ n * Rfac t j * ∏ r ∈ Finset.range n, (t ^ (j + r + 1) - 1))
      * hunit - (-1 : ℝ) ^ n * hsplit

/-- `∏_{i ≠ j, i ≤ n} (q^j - q^i)`, cleared of negative powers.  The exponent
`n·j + C(n-j+1, 2)` is where the `j`-dependence that must cancel comes from. -/
private theorem node_denom {t : ℝ} (ht : 1 < t) {n j : ℕ} (hj : j ≤ n) :
    t ^ (n * j + (n - j + 1).choose 2)
        * ∏ i ∈ (Finset.range (n + 1)).erase j, ((t⁻¹) ^ j - (t⁻¹) ^ i)
      = (-1) ^ j * (Rfac t j * Rfac t (n - j)) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt ht0
  have hqt : ∀ k : ℕ, t ^ k * (t⁻¹) ^ k = 1 := fun k => by
    rw [← mul_pow, mul_inv_cancel₀ htne, one_pow]
  have hsplit : (Finset.range (n + 1)).erase j
      = Finset.range j ∪ Finset.Ico (j + 1) (n + 1) := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range j) (Finset.Ico (j + 1) (n + 1)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Ico] at hb
    omega
  have hlow : ∏ i ∈ Finset.range j, ((t⁻¹) ^ j - (t⁻¹) ^ i)
      = (-1) ^ j * ((t⁻¹) ^ j) ^ j * Rfac t j := by
    have hfac : ∀ i ∈ Finset.range j,
        ((t⁻¹) ^ j - (t⁻¹) ^ i) = (-(t⁻¹) ^ j) * (t ^ (j - 1 - i + 1) - 1) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      have hidx : j - 1 - i + 1 = j - i := by omega
      have hij : i + (j - i) = j := by omega
      have e1 : (t⁻¹) ^ j * t ^ (j - i) = (t⁻¹) ^ i := by
        calc (t⁻¹) ^ j * t ^ (j - i) = (t⁻¹) ^ (i + (j - i)) * t ^ (j - i) := by rw [hij]
          _ = (t⁻¹) ^ i * ((t⁻¹) ^ (j - i) * t ^ (j - i)) := by rw [pow_add]; ring
          _ = (t⁻¹) ^ i := by rw [← mul_pow, inv_mul_cancel₀ htne, one_pow, mul_one]
      rw [hidx]
      linear_combination e1
    simp only [Rfac]
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range, Finset.prod_range_reflect (fun i => t ^ (i + 1) - 1) j, neg_pow]
  have hhigh : ∏ i ∈ Finset.Ico (j + 1) (n + 1), ((t⁻¹) ^ j - (t⁻¹) ^ i)
      = ((t⁻¹) ^ j) ^ (n - j) * (t⁻¹) ^ ((n - j + 1).choose 2) * Rfac t (n - j) := by
    rw [Finset.prod_Ico_eq_prod_range, show n + 1 - (j + 1) = n - j from by omega]
    have hfac : ∀ u ∈ Finset.range (n - j),
        ((t⁻¹) ^ j - (t⁻¹) ^ (j + 1 + u))
          = (t⁻¹) ^ j * ((t⁻¹) ^ (u + 1) * (t ^ (u + 1) - 1)) := by
      intro u _
      have e1 : (t⁻¹) ^ (j + 1 + u) = (t⁻¹) ^ j * (t⁻¹) ^ (u + 1) := by
        rw [← pow_add]; congr 1; omega
      have e2 : (t⁻¹) ^ (u + 1) * t ^ (u + 1) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ htne, one_pow]
      rw [e1]
      linear_combination (-(t⁻¹) ^ j) * e2
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      sum_range_succ_choose]
    simp only [Rfac]
    ring
  rw [hsplit, Finset.prod_union hdisj, hlow, hhigh]
  have hcollect : ((t⁻¹) ^ j) ^ j * (((t⁻¹) ^ j) ^ (n - j) * (t⁻¹) ^ ((n - j + 1).choose 2))
      = (t⁻¹) ^ (n * j + (n - j + 1).choose 2) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    have hjj : j * j + j * (n - j) = n * j := by
      have h1 : j * j + j * (n - j) = j * (j + (n - j)) := by ring
      rw [h1, Nat.add_sub_cancel' hj, Nat.mul_comm]
    rw [← Nat.add_assoc, hjj]
  have hone := hqt (n * j + (n - j + 1).choose 2)
  linear_combination
    ((-1 : ℝ) ^ j * Rfac t j * Rfac t (n - j) * t ^ (n * j + (n - j + 1).choose 2)) * hcollect
      + ((-1 : ℝ) ^ j * Rfac t j * Rfac t (n - j)) * hone

/-- **The crux.**  The Lagrange coefficient at the node `q^j` is `legGamma t n j` times the
`j`-independent scalar `(-1)^n t^{n(n+1)/2}`.  Verified symbolically (sympy, `n = 1..5`, every
`j`, exact) before being formalised. -/
private theorem lagrange_coef {t : ℝ} (ht : 1 < t) {n j : ℕ} (hj : j ≤ n) :
    (∏ r ∈ Finset.range n, ((t⁻¹) ^ j - t ^ (r + 1)))
      = (-1) ^ n * t ^ ((n + 1).choose 2) * legGamma t n j
          * ∏ i ∈ (Finset.range (n + 1)).erase j, ((t⁻¹) ^ j - (t⁻¹) ^ i) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt ht0
  have hRj := Rfac_ne_zero ht j
  have hRnj := Rfac_ne_zero ht (n - j)
  have hu : ((-1 : ℝ)) ^ j * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
  have hA := Nprod_eval ht n j
  have hB := node_denom ht hj
  have hG := gauss_prod ht hj
  have hgam : legGamma t n j * t ^ (n * j) = legCoef t n j := by
    rw [legGamma, ← pow_mul, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ htne), mul_one]
  have hE : t ^ ((n + 1).choose 2) * t ^ (j.choose 2)
      = t ^ (n * j + (n - j + 1).choose 2) := by
    rw [← pow_add]
    congr 1
    exact (tri_key hj).symm.trans (Nat.add_comm _ _)
  have hgg : gauss t n j * gauss t (n + j) n
      = Rfac t (n + j) / (Rfac t j * Rfac t j * Rfac t (n - j)) := by
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero hRj hRj) hRnj)]
    linear_combination hG
  have hNv : (∏ r ∈ Finset.range n, ((t⁻¹) ^ j - t ^ (r + 1)))
      = (-1) ^ n * Rfac t (n + j) / (Rfac t j * t ^ (n * j)) := by
    rw [eq_div_iff (mul_ne_zero hRj (pow_ne_zero _ htne))]
    linear_combination hA
  have hGam' : ((-1 : ℝ)) ^ j * legGamma t n j
      = t ^ (j.choose 2) * (Rfac t (n + j) / (Rfac t j * Rfac t j * Rfac t (n - j)))
          / t ^ (n * j) := by
    rw [eq_div_iff (pow_ne_zero _ htne), mul_assoc, hgam, legCoef, ← hgg]
    linear_combination (t ^ (j.choose 2) * gauss t n j * gauss t (n + j) n) * hu
  have hDv' : ((-1 : ℝ)) ^ j * (∏ i ∈ (Finset.range (n + 1)).erase j, ((t⁻¹) ^ j - (t⁻¹) ^ i))
      = (Rfac t j * Rfac t (n - j)) / (t ^ ((n + 1).choose 2) * t ^ (j.choose 2)) := by
    rw [hE, eq_div_iff (pow_ne_zero _ htne)]
    linear_combination (Rfac t j * Rfac t (n - j)) * hu + ((-1 : ℝ) ^ j) * hB
  calc (∏ r ∈ Finset.range n, ((t⁻¹) ^ j - t ^ (r + 1)))
      = (-1) ^ n * Rfac t (n + j) / (Rfac t j * t ^ (n * j)) := hNv
    _ = (-1) ^ n * t ^ ((n + 1).choose 2) * (((-1 : ℝ)) ^ j * legGamma t n j)
          * (((-1 : ℝ)) ^ j
              * ∏ i ∈ (Finset.range (n + 1)).erase j, ((t⁻¹) ^ j - (t⁻¹) ^ i)) := by
        rw [hGam', hDv']
        field_simp
    _ = (-1) ^ n * t ^ ((n + 1).choose 2) * legGamma t n j
          * ∏ i ∈ (Finset.range (n + 1)).erase j, ((t⁻¹) ^ j - (t⁻¹) ^ i) := by
        linear_combination
          ((-1 : ℝ) ^ n * t ^ ((n + 1).choose 2) * legGamma t n j
            * ∏ i ∈ (Finset.range (n + 1)).erase j, ((t⁻¹) ^ j - (t⁻¹) ^ i)) * hu

/-! ## Step 4 — the finite orthogonality relation -/

/-- **The moment in closed form, for every `m`.**  This is `cauchy_lagrange` specialised to
`y j = q^j`, `z = t^{m+1}`, `N = ∏_{r<n} (X - t^{r+1})`, with the Lagrange coefficients replaced
by `legGamma` through `lagrange_coef`.  No hypothesis relating `m` and `n` is needed. -/
theorem orth_moment {t : ℝ} (ht : 1 < t) (n m : ℕ) :
    ((-1) ^ n * t ^ ((n + 1).choose 2))
        * ∑ j ∈ Finset.range (n + 1), legGamma t n j * t ^ j / (t ^ (m + j + 1) - 1)
      = (∏ r ∈ Finset.range n, (t ^ (m + 1) - t ^ (r + 1)))
          / ∏ j ∈ Finset.range (n + 1), (t ^ (m + 1) - (t⁻¹) ^ j) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt ht0
  have hinv0 : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht0
  have hinv1 : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
  -- injectivity of the nodes
  have hinjg : Function.Injective (fun k : ℕ => (t⁻¹) ^ k) :=
    pow_right_injective₀ hinv0 (ne_of_lt hinv1)
  have hinj : Set.InjOn (fun k : ℕ => (t⁻¹) ^ k) (Finset.range (n + 1)) := hinjg.injOn
  -- the nodal polynomial of the *other* node set
  have hdeg : (Lagrange.nodal (Finset.range n) (fun r : ℕ => t ^ (r + 1))).degree
      < (Finset.range (n + 1)).card := by
    rw [Lagrange.degree_nodal, Finset.card_range, Finset.card_range]
    exact_mod_cast Nat.lt_succ_self n
  have hone : ∀ k : ℕ, (t⁻¹) ^ k ≤ 1 := fun k => pow_le_one₀ (le_of_lt hinv0) (le_of_lt hinv1)
  have hzgt : (1 : ℝ) < t ^ (m + 1) := one_lt_pow₀ ht (Nat.succ_ne_zero m)
  have hz : ∀ j ∈ Finset.range (n + 1), t ^ (m + 1) ≠ (fun k : ℕ => (t⁻¹) ^ k) j := by
    intro j _
    have := hone j
    simp only
    intro hEq
    rw [hEq] at hzgt
    linarith
  have hlag := cauchy_lagrange (Finset.range (n + 1)) (fun k : ℕ => (t⁻¹) ^ k) hinj
      (Lagrange.nodal (Finset.range n) (fun r : ℕ => t ^ (r + 1))) hdeg (t ^ (m + 1)) hz
  simp only [Lagrange.eval_nodal] at hlag
  rw [← hlag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by
    have := Finset.mem_range.mp hj
    omega
  -- the denominator product is nonzero
  have hDne : (∏ i ∈ (Finset.range (n + 1)).erase j, ((t⁻¹) ^ j - (t⁻¹) ^ i)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    obtain ⟨hij, his⟩ := Finset.mem_erase.mp hi
    exact sub_ne_zero_of_ne fun hEq => hij (hinjg hEq.symm)
  have hznej : t ^ (m + 1) - (t⁻¹) ^ j ≠ 0 := by
    have := hone j
    intro hEq
    have : t ^ (m + 1) = (t⁻¹) ^ j := by linarith [sub_eq_zero.mp hEq]
    rw [this] at hzgt
    linarith [hone j]
  have hdenpos : (0 : ℝ) < t ^ (m + j + 1) - 1 := by
    have : (1 : ℝ) < t ^ (m + j + 1) := one_lt_pow₀ ht (by omega)
    linarith
  have hzy : (t ^ (m + 1) - (t⁻¹) ^ j) * t ^ j = t ^ (m + j + 1) - 1 := by
    have e1 : t ^ (m + 1) * t ^ j = t ^ (m + j + 1) := by rw [← pow_add]; congr 1; omega
    have e2 : (t⁻¹) ^ j * t ^ j = 1 := by rw [← mul_pow, inv_mul_cancel₀ htne, one_pow]
    linear_combination e1 - e2
  have hkey : legGamma t n j * t ^ j / (t ^ (m + j + 1) - 1)
      = legGamma t n j / (t ^ (m + 1) - (t⁻¹) ^ j) := by
    rw [div_eq_div_iff (ne_of_gt hdenpos) hznej]
    linear_combination (legGamma t n j) * hzy
  rw [lagrange_coef ht hjn, hkey, ← mul_div_assoc,
    div_eq_div_iff hznej (mul_ne_zero hDne hznej)]
  ring

/-- **Orthogonality, finite form.**  For `m < n` the little q-Legendre polynomial `P_n` is
annihilated by the functional `x ↦ L(x^m ·)`; in the explicit coefficient form this reads
`∑_{j≤n} γ_{n,j} t^j / (t^{m+j+1} - 1) = 0`. -/
theorem orth_finset {t : ℝ} (ht : 1 < t) {n m : ℕ} (hm : m < n) :
    ∑ j ∈ Finset.range (n + 1),
      legGamma t n j * t ^ j / (t ^ (m + j + 1) - 1) = 0 := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt ht0
  have hnum : (∏ r ∈ Finset.range n, (t ^ (m + 1) - t ^ (r + 1))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_range.mpr hm) (by ring)
  have h := orth_moment ht n m
  rw [hnum, zero_div] at h
  have hC : ((-1 : ℝ)) ^ n * t ^ ((n + 1).choose 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ htne)
  exact (mul_eq_zero.mp h).resolve_left hC

/-- **The `n`-th moment.**  `m = n` in `orth_moment`; the numerator no longer vanishes, so this
is an explicit closed product form for `L(x^n P_n)` up to the scalar. -/
theorem moment_n {t : ℝ} (ht : 1 < t) (n : ℕ) :
    ((-1) ^ n * t ^ ((n + 1).choose 2))
        * ∑ j ∈ Finset.range (n + 1), legGamma t n j * t ^ j / (t ^ (n + j + 1) - 1)
      = (∏ r ∈ Finset.range n, (t ^ (n + 1) - t ^ (r + 1)))
          / ∏ j ∈ Finset.range (n + 1), (t ^ (n + 1) - (t⁻¹) ^ j) :=
  orth_moment ht n n

/-! ## Step 5 — the series forms -/

/-- `P_n(q^k) = ∑_j γ_{n,j} (q^k)^j` — `legG` in the rescaled variable, evaluated on the
lattice. -/
theorem legG_lattice (t : ℝ) (n k : ℕ) :
    legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹)
      = ∑ j ∈ Finset.range (n + 1), legGamma t n j * ((t⁻¹) ^ k) ^ j := by
  simp only [legG, legGamma, mul_pow, inv_pow]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem lattice_term (t : ℝ) (n p k : ℕ) :
    ((t⁻¹) ^ k) ^ (p + 1) * legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹)
      = ∑ j ∈ Finset.range (n + 1), legGamma t n j * ((t⁻¹) ^ (p + j + 1)) ^ k := by
  rw [legG_lattice, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ((t⁻¹) ^ k) ^ (p + 1) * ((t⁻¹) ^ k) ^ j = ((t⁻¹) ^ (p + j + 1)) ^ k := by
    rw [← pow_add, ← pow_mul, ← pow_mul]
    congr 1
    ring
  linear_combination (legGamma t n j) * h

/-- Summability of the lattice terms — a finite sum of geometric series with ratio `< 1`. -/
theorem summable_lattice {t : ℝ} (ht : 1 < t) (n p : ℕ) :
    Summable (fun k : ℕ => ((t⁻¹) ^ k) ^ (p + 1) * legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹)) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt ht0
  have hinv0 : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht0
  have hinv1 : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
  simp only [lattice_term t n p]
  refine summable_sum fun j _ => ?_
  exact (summable_geometric_of_lt_one (pow_nonneg (le_of_lt hinv0) _)
    (pow_lt_one₀ (le_of_lt hinv0) hinv1 (by omega))).mul_left _

/-- **The series moment, for every `m`.**  `L(x^m P_n) = t^{m+1} ∑_j γ_{n,j} t^j/(t^{m+j+1}-1)`. -/
theorem moment_tsum {t : ℝ} (ht : 1 < t) (n p : ℕ) :
    ∑' k : ℕ, ((t⁻¹) ^ k) ^ (p + 1) * legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹)
      = t ^ (p + 1)
        * ∑ j ∈ Finset.range (n + 1), legGamma t n j * t ^ j / (t ^ (p + j + 1) - 1) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt ht0
  have hinv0 : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht0
  have hinv1 : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
  simp only [lattice_term t n p]
  rw [Summable.tsum_finsetSum fun j _ =>
    (summable_geometric_of_lt_one (pow_nonneg (le_of_lt hinv0) _)
      (pow_lt_one₀ (le_of_lt hinv0) hinv1 (by omega))).mul_left _]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (pow_nonneg (le_of_lt hinv0) _)
    (pow_lt_one₀ (le_of_lt hinv0) hinv1 (by omega))]
  have hdenpos : (0 : ℝ) < t ^ (p + j + 1) - 1 := by
    have : (1 : ℝ) < t ^ (p + j + 1) := one_lt_pow₀ ht (by omega)
    linarith
  have hstep : (1 : ℝ) - (t⁻¹) ^ (p + j + 1) = (t ^ (p + j + 1) - 1) / t ^ (p + j + 1) := by
    rw [inv_pow]
    field_simp
  rw [hstep, inv_div]
  have hpj : t ^ (p + 1) * t ^ j = t ^ (p + j + 1) := by rw [← pow_add]; congr 1; omega
  field_simp
  linear_combination (legGamma t n j) * hpj

/-- **Orthogonality, series form.**  The statement `QHarm/Pade.lean` consumes. -/
theorem orth_tsum {t : ℝ} (ht : 1 < t) {n m : ℕ} (hm : m < n) :
    ∑' k : ℕ, ((t⁻¹) ^ k) ^ (m + 1) * legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹) = 0 := by
  rw [moment_tsum ht n m, orth_finset ht hm, mul_zero]

/-- **Linear-combination form.**  Any polynomial of degree `< n` is annihilated — the shape the
add-and-subtract in `QHarm/Forms.lean` needs. -/
theorem orth_tsum_lt {t : ℝ} (ht : 1 < t) {n : ℕ} (c : ℕ → ℝ) :
    ∑' k : ℕ, (t⁻¹) ^ k * (∑ m ∈ Finset.range n, c m * ((t⁻¹) ^ k) ^ m)
        * legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹) = 0 := by
  have hrw : ∀ k : ℕ,
      (t⁻¹) ^ k * (∑ m ∈ Finset.range n, c m * ((t⁻¹) ^ k) ^ m)
          * legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹)
        = ∑ m ∈ Finset.range n,
            c m * (((t⁻¹) ^ k) ^ (m + 1) * legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹)) := by
    intro k
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  simp only [hrw]
  rw [Summable.tsum_finsetSum fun m _ => (summable_lattice ht n m).mul_left (c m)]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [tsum_mul_left, orth_tsum ht (Finset.mem_range.mp hm), mul_zero]

/-- **The squared norm reduces to the `n`-th moment.**  `h_n = γ_{n,n} · L(x^n P_n)`, because
`P_n = γ_{n,n} x^n + (lower)` and the lower part is annihilated by `orth_finset`. -/
theorem norm_sq_eq {t : ℝ} (ht : 1 < t) (n : ℕ) :
    ∑' k : ℕ, (t⁻¹) ^ k * (legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹)) ^ 2
      = legGamma t n n
        * (t ^ (n + 1)
            * ∑ j ∈ Finset.range (n + 1), legGamma t n j * t ^ j / (t ^ (n + j + 1) - 1)) := by
  have hrw : ∀ k : ℕ,
      (t⁻¹) ^ k * (legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹)) ^ 2
        = ∑ i ∈ Finset.range (n + 1),
            legGamma t n i * (((t⁻¹) ^ k) ^ (i + 1) * legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹)) := by
    intro k
    have h1 : (legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹)) ^ 2
        = (∑ i ∈ Finset.range (n + 1), legGamma t n i * ((t⁻¹) ^ k) ^ i)
            * legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹) := by
      rw [← legG_lattice]; ring
    rw [h1, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [hrw]
  rw [Summable.tsum_finsetSum fun i _ => (summable_lattice ht n i).mul_left (legGamma t n i)]
  rw [Finset.sum_eq_single n]
  · rw [tsum_mul_left, moment_tsum ht n n]
  · intro i hi hne
    rw [tsum_mul_left, moment_tsum ht n i,
      orth_finset ht (lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne),
      mul_zero, mul_zero]
  · intro hn
    exact absurd (Finset.self_mem_range_succ n) hn


/-! ## Step 6 — the exact squared norm

`norm_sq_eq` reduces `h_n` to the `n`-th moment; `moment_n` gives that moment as a quotient of
node products.  Both products evaluate in closed form through `Rfac`, and the answer is
Van Assche's `h_n = q^n/(1 - q^{2n+1}) = t^{n+1}/(t^{2n+1} - 1)`.  This is delivered as an exact
identity, not a bound: it is strictly stronger than the `h_n ≤ t^{2n}` the assembly needs (the
true value is `≈ t^{-n}`, roughly `t^{3n}` of headroom). -/

private theorem sum_range_id_choose (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), j = (n + 1).choose 2 := by
  rw [Finset.sum_range_succ']
  simpa using sum_range_succ_choose n

/-- The numerator of `moment_n`: `∏_{r<n} (t^{n+1} - t^{r+1}) = t^{n(n+1)/2} [n]_t!`. -/
private theorem nodal_num {t : ℝ} (n : ℕ) :
    (∏ r ∈ Finset.range n, (t ^ (n + 1) - t ^ (r + 1)))
      = t ^ ((n + 1).choose 2) * Rfac t n := by
  have hfac : ∀ r ∈ Finset.range n,
      (t ^ (n + 1) - t ^ (r + 1)) = t ^ (r + 1) * (t ^ (n - 1 - r + 1) - 1) := by
    intro r hr
    simp only [Finset.mem_range] at hr
    have hidx : n - 1 - r + 1 = n - r := by omega
    have hsum : t ^ (r + 1) * t ^ (n - r) = t ^ (n + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hidx]
    linear_combination -hsum
  simp only [Rfac]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    sum_range_succ_choose, Finset.prod_range_reflect (fun i => t ^ (i + 1) - 1) n]

/-- The denominator of `moment_n`: `t^{n(n+1)/2} · ∏_{j≤n}(t^{n+1} - q^j) · [n]_t! = [2n+1]_t!`. -/
private theorem nodal_den {t : ℝ} (htne : t ≠ 0) (n : ℕ) :
    t ^ ((n + 1).choose 2) * (∏ j ∈ Finset.range (n + 1), (t ^ (n + 1) - (t⁻¹) ^ j))
        * Rfac t n
      = Rfac t (2 * n + 1) := by
  have hfac : ∀ j ∈ Finset.range (n + 1),
      (t ^ (n + 1) - (t⁻¹) ^ j) = (t⁻¹) ^ j * (t ^ (n + j + 1) - 1) := by
    intro j _
    have e1 : (t⁻¹) ^ j * t ^ (n + j + 1) = t ^ (n + 1) := by
      have hp : t ^ (n + j + 1) = t ^ j * t ^ (n + 1) := by rw [← pow_add]; congr 1; omega
      rw [hp, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ htne, one_pow, one_mul]
    linear_combination -e1
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    sum_range_id_choose]
  have hsplit := Rfac_split t n (n + 1)
  rw [show n + (n + 1) = 2 * n + 1 from by omega] at hsplit
  rw [hsplit]
  have hunit : t ^ ((n + 1).choose 2) * (t⁻¹) ^ ((n + 1).choose 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ htne, one_pow]
  linear_combination
    (Rfac t n * ∏ i ∈ Finset.range (n + 1), (t ^ (n + i + 1) - 1)) * hunit

theorem gauss_diag {t : ℝ} (ht : 1 < t) (n : ℕ) : gauss t n n = 1 := by
  have h := gauss_mul_Rfac ht (le_refl n)
  rw [Nat.sub_self, Rfac_zero, mul_one] at h
  have h2 : gauss t n n * Rfac t n = 1 * Rfac t n := by rw [one_mul]; exact h
  exact mul_right_cancel₀ (Rfac_ne_zero ht n) h2

/-- The leading coefficient `γ_{n,n}` in closed form. -/
private theorem legGamma_diag {t : ℝ} (ht : 1 < t) (n : ℕ) :
    ((-1 : ℝ)) ^ n * legGamma t n n
      = t ^ (n.choose 2) * Rfac t (2 * n) / (t ^ (n * n) * (Rfac t n * Rfac t n)) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt ht0
  have hA := Rfac_ne_zero ht n
  have hu : ((-1 : ℝ)) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hinv : (t ^ (n * n))⁻¹ * t ^ (n * n) = 1 := inv_mul_cancel₀ (pow_ne_zero _ htne)
  have hgnn : gauss t (n + n) n * Rfac t n * Rfac t n = Rfac t (2 * n) := by
    have h := gauss_mul_Rfac ht (Nat.le_add_left n n)
    rw [show n + n - n = n from by omega] at h
    rw [show (2 * n) = n + n from by omega]
    exact h
  rw [eq_div_iff (mul_ne_zero (pow_ne_zero _ htne) (mul_ne_zero hA hA)),
    legGamma, legCoef, gauss_diag ht n, ← pow_mul, ← hgnn]
  linear_combination
    (t ^ (n.choose 2) * gauss t (n + n) n * Rfac t n * Rfac t n
      * (t ^ (n * n))⁻¹ * t ^ (n * n)) * hu
    + (t ^ (n.choose 2) * gauss t (n + n) n * Rfac t n * Rfac t n) * hinv

/-- The `n`-th moment as a ratio of `t`-factorials. -/
private theorem moment_n_prod {t : ℝ} (ht : 1 < t) (n : ℕ) :
    ((-1 : ℝ)) ^ n
        * (∑ j ∈ Finset.range (n + 1), legGamma t n j * t ^ j / (t ^ (n + j + 1) - 1))
      = t ^ ((n + 1).choose 2) * (Rfac t n * Rfac t n) / Rfac t (2 * n + 1) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt ht0
  have hR := Rfac_ne_zero ht (2 * n + 1)
  have hden := nodal_den htne n
  have hdenne : (∏ j ∈ Finset.range (n + 1), (t ^ (n + 1) - (t⁻¹) ^ j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    have h1 : (1 : ℝ) < t ^ (n + 1) := one_lt_pow₀ ht (Nat.succ_ne_zero n)
    have h2 : (t⁻¹) ^ j ≤ 1 :=
      pow_le_one₀ (le_of_lt (inv_pos.mpr ht0)) (le_of_lt (inv_lt_one_of_one_lt₀ ht))
    intro h0
    have := sub_eq_zero.mp h0
    linarith
  have h := moment_n ht n
  rw [nodal_num n, eq_div_iff hdenne] at h
  rw [eq_div_iff hR, ← hden]
  linear_combination (Rfac t n) * h

/-- **The squared norm, exactly.**  `h_n = ∑_k q^k P_n(q^k)^2 = t^{n+1}/(t^{2n+1} - 1)`, i.e.
Van Assche's `q^n/(1 - q^{2n+1})`.  Checked independently on exact rationals
(`t ∈ {2,3,5,7}`, `n ≤ 7`) before formalisation. -/
theorem norm_sq_value {t : ℝ} (ht : 1 < t) (n : ℕ) :
    ∑' k : ℕ, (t⁻¹) ^ k * (legG t n ((t⁻¹) ^ k * (t ^ n)⁻¹)) ^ 2
      = t ^ (n + 1) / (t ^ (2 * n + 1) - 1) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt ht0
  have hA := Rfac_ne_zero ht n
  have hB := Rfac_ne_zero ht (2 * n)
  have hD : t ^ (2 * n + 1) - 1 ≠ 0 := by
    have : (1 : ℝ) < t ^ (2 * n + 1) := one_lt_pow₀ ht (by omega)
    linarith
  have hu : ((-1 : ℝ)) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hRD : Rfac t (2 * n + 1) = Rfac t (2 * n) * (t ^ (2 * n + 1) - 1) := by
    simp only [Rfac]
    rw [Finset.prod_range_succ]
  have hexpP : t ^ (n.choose 2) * t ^ ((n + 1).choose 2) = t ^ (n * n) := by
    rw [← pow_add]
    congr 1
    rw [choose_two_succ, ← two_choose_two_add n]
    omega
  rw [norm_sq_eq ht n]
  have hsq : legGamma t n n
        * (t ^ (n + 1)
            * ∑ j ∈ Finset.range (n + 1), legGamma t n j * t ^ j / (t ^ (n + j + 1) - 1))
      = t ^ (n + 1) * (((-1 : ℝ)) ^ n * legGamma t n n)
        * (((-1 : ℝ)) ^ n
            * ∑ j ∈ Finset.range (n + 1), legGamma t n j * t ^ j / (t ^ (n + j + 1) - 1)) := by
    linear_combination
      (-(t ^ (n + 1) * legGamma t n n
        * ∑ j ∈ Finset.range (n + 1), legGamma t n j * t ^ j / (t ^ (n + j + 1) - 1))) * hu
  rw [hsq, legGamma_diag ht n, moment_n_prod ht n, hRD, ← hexpP]
  field_simp

#print axioms QHarm.orth_finset
#print axioms QHarm.orth_tsum
#print axioms QHarm.orth_moment
#print axioms QHarm.orth_tsum_lt
#print axioms QHarm.moment_n
#print axioms QHarm.norm_sq_eq
#print axioms QHarm.norm_sq_value
#print axioms QHarm.cauchy_lagrange

end QHarm
