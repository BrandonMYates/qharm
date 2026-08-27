/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QHarm.Legendre
import QHarm.Integrality

/-!
# QHarm/RatDecomp.lean — the A-form decomposition

This file contains the exact algebraic identity that replaces
Van Assche's equation (25) in the rational-base track.

## The problem this solves

`QHarm/Integrality.lean`'s `legQval_eq_flat` writes `Q_n(t^n)` as a double sum whose `(j,d)` term
carries `t^{-(n-1)d}`.  Over `ℤ` (deviation D6) that is fixed by the extra clearing `t^{M_n}`.
Over `ℚ`, `t = P/Q`, the same term carries a **`P`-denominator** `P^{(n-1)d}` against a
`P`-numerator of only `P^{C(j,2)}`, and the D6 fix costs `P^{n²/2}`, which pushes the threshold
from `1/2 − 1/π² ≈ 0.3987` down to `0.232`.

## What is proved here

`Aform_decomp`: for every real `t > 1` and every `n`,

    Q_n(t^n) + P_n(t^n) · head_n
      =  − ∑_{j≤n} j · legCoef t n j
         + ∑_{r=1}^{n-1} P_n(t^{n-r}) / (t^r − 1)
         + ∑_{d=1}^{n} (∑_{j≥d} legCoef t n j) · t^d/(t^d − 1)

with `P_n(t^{n-r}) = legG t n ((t^r)⁻¹)`.  **Every negative power of `t` has disappeared.**  The
head sum cancels *exactly* against the `legVal` half of the regrouped double sum — that is the
whole content, and it is why no extra `P`-power is needed.

Downstream, each of the three pieces is cleared by `Q^{C_n} · 𝒟_n` term by term:

* `∑_j j·legCoef` — by `Q^{C_n}` alone (`QHarm/RatSetup.lean`);
* `t^d/(t^d−1) = P^d/(P^d − Q^d)` and the tail sums — by `𝒟_n` and `Q^{C_n}`;
* `1/(t^r−1) = Q^r/(P^r − Q^r)` by `𝒟_n`, and `Q^{C_n}·legG t n ((t^r)⁻¹) ∈ ℤ` by the closed
  form of `QHarm/QLagrange.lean`.

## Consumes

`QHarm/Legendre.lean` (`legCoef`, `legG`, `legVal`, `legQval`, `headSum`) and
`QHarm/Integrality.lean` (`legQval_eq_flat` only).

## Main results

* `legTail` — the tail sums `T_d = ∑_{j=d}^{n} legCoef t n j`;
* `geom_split` — the per-`d` partial-fraction identity;
* `tail_sum_zero`, `tail_sum_pos` — the two evaluations of `∑_d T_d t^{-rd}`;
* `Aform_decomp` — the identity above.

## What is NOT here

No integrality (that is `QHarm/RatSetup.lean` / `QHarm/RatIntegrality.lean`), no size bound, no
closed form for `legG t n ((t^r)⁻¹)` (that is `QHarm/QLagrange.lean`).  This file is pure real
algebra and holds for every real `t > 1`, rational or not.
-/

namespace QHarm

open Finset

/-- The tail sums `T_d = ∑_{j=d}^{n} legCoef t n j`. -/
noncomputable def legTail (t : ℝ) (n d : ℕ) : ℝ := ∑ j ∈ Finset.Icc d n, legCoef t n j

section

variable {t : ℝ}

private theorem tpos (ht : 1 < t) : (0 : ℝ) < t := lt_trans zero_lt_one ht

private theorem psub_pos (ht : 1 < t) {d : ℕ} (hd : 1 ≤ d) : (0 : ℝ) < t ^ d - 1 := by
  have h : (1 : ℝ) < t ^ d := one_lt_pow₀ ht (by omega)
  linarith

private theorem psub_ne (ht : 1 < t) {d : ℕ} (hd : 1 ≤ d) : (t : ℝ) ^ d - 1 ≠ 0 :=
  ne_of_gt (psub_pos ht hd)

/-! ### Step 1 — the per-`d` partial fraction

`t^{-p d}/(t^d − 1) + ∑_{r=0}^{p} t^{-r d} = t^d/(t^d − 1)`.

This is the identity that turns the negative powers of `t` in `legQval_eq_flat` into the
positive-power form `t^d/(t^d − 1)` at the cost of the geometric block `∑_r t^{-rd}`, which is
what will later reassemble into `legG t n ((t^r)⁻¹)` and the head sum. -/

/-- The abstract shape: `x` and `y` reciprocal, `y ≠ 1`. -/
private theorem geom_split_abstract {x y : ℝ} (hxy : x * y = 1) (hy1 : y - 1 ≠ 0) (p : ℕ) :
    x ^ p * (y - 1)⁻¹ + ∑ r ∈ Finset.range (p + 1), x ^ r = y / (y - 1) := by
  have hgeo := geom_sum_mul x (p + 1)
  rw [pow_succ] at hgeo
  have key : x ^ p + (∑ r ∈ Finset.range (p + 1), x ^ r) * (y - 1) = y := by
    linear_combination (-y) * hgeo + ((∑ r ∈ Finset.range (p + 1), x ^ r) - x ^ p) * hxy
  have hinv : (y - 1)⁻¹ * (y - 1) = 1 := inv_mul_cancel₀ hy1
  rw [eq_div_iff hy1, add_mul, mul_assoc, hinv, mul_one]
  exact key

theorem geom_split (ht : 1 < t) (p : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    (t ^ (p * d))⁻¹ * (t ^ d - 1)⁻¹ + ∑ r ∈ Finset.range (p + 1), (t ^ (r * d))⁻¹
      = t ^ d / (t ^ d - 1) := by
  have ht0 := tpos ht
  have hy0 : (t : ℝ) ^ d ≠ 0 := ne_of_gt (pow_pos ht0 d)
  have hyne : (t : ℝ) ^ d - 1 ≠ 0 := psub_ne ht hd
  have hrw : ∀ r : ℕ, ((t : ℝ) ^ (r * d))⁻¹ = (((t : ℝ) ^ d)⁻¹) ^ r := by
    intro r
    rw [inv_pow, ← pow_mul, Nat.mul_comm d r]
  rw [hrw p, Finset.sum_congr rfl (fun r _ => hrw r)]
  exact geom_split_abstract (inv_mul_cancel₀ hy0) hyne p

/-- The finite geometric block, abstract shape. -/
private theorem geom_finite_abstract {x y : ℝ} (hxy : x * y = 1) (hy1 : y - 1 ≠ 0) (j : ℕ) :
    (∑ d ∈ Finset.range j, x ^ d) * x = (1 - x ^ j) / (y - 1) := by
  have hgeo := geom_sum_mul x j
  rw [eq_div_iff hy1]
  linear_combination (-1 : ℝ) * hgeo + (∑ d ∈ Finset.range j, x ^ d) * hxy

/-! ### Step 2 — the two evaluations of `∑_{d=1}^{n} T_d t^{-rd}` -/

/-- `r = 0`: the tail sums add up to `∑_j j · legCoef t n j`. -/
theorem tail_sum_zero (t : ℝ) (n : ℕ) :
    ∑ d ∈ Finset.range n, legTail t n (d + 1)
      = ∑ j ∈ Finset.range (n + 1), (j : ℝ) * legCoef t n j := by
  unfold legTail
  rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun j => Finset.range j)
    (h := by
      intro d j
      simp only [Finset.mem_range, Finset.mem_Icc]
      omega)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `r ≥ 1`: the tail sums resum to `(P_n(t^n) − P_n(t^{n-r}))/(t^r − 1)`. -/
theorem tail_sum_pos (ht : 1 < t) (n : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    ∑ d ∈ Finset.range n, legTail t n (d + 1) * (t ^ ((d + 1) * r))⁻¹
      = (legVal t n - legG t n ((t ^ r)⁻¹)) / (t ^ r - 1) := by
  have ht0 := tpos ht
  have hrne : (t : ℝ) ^ r - 1 ≠ 0 := psub_ne ht hr
  have hr0 : (t : ℝ) ^ r ≠ 0 := ne_of_gt (pow_pos ht0 r)
  -- swap the order of summation
  have hswap :
      ∑ d ∈ Finset.range n, legTail t n (d + 1) * (t ^ ((d + 1) * r))⁻¹
        = ∑ j ∈ Finset.range (n + 1),
            ∑ d ∈ Finset.range j, legCoef t n j * (t ^ ((d + 1) * r))⁻¹ := by
    unfold legTail
    rw [Finset.sum_congr rfl (fun d _ => Finset.sum_mul _ _ _)]
    exact Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun j => Finset.range j)
      (h := by
        intro d j
        simp only [Finset.mem_range, Finset.mem_Icc]
        omega)
  rw [hswap]
  -- the inner geometric sum
  have hinner : ∀ j : ℕ,
      ∑ d ∈ Finset.range j, legCoef t n j * ((t : ℝ) ^ ((d + 1) * r))⁻¹
        = legCoef t n j * ((1 - (((t : ℝ) ^ r)⁻¹) ^ j) / ((t : ℝ) ^ r - 1)) := by
    intro j
    rw [← Finset.mul_sum]
    congr 1
    have hrw : ∀ d : ℕ, ((t : ℝ) ^ ((d + 1) * r))⁻¹
        = (((t : ℝ) ^ r)⁻¹) ^ d * ((t : ℝ) ^ r)⁻¹ := by
      intro d
      rw [← pow_succ, inv_pow, ← pow_mul, Nat.mul_comm r (d + 1)]
    rw [Finset.sum_congr rfl (fun d _ => hrw d), ← Finset.sum_mul]
    exact geom_finite_abstract (inv_mul_cancel₀ hr0) hrne j
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  -- split into legVal and legG
  rw [legVal_eq]
  unfold legG
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### Step 3 — the decomposition -/

/-- **The A-form decomposition.**  Verified in exact rational arithmetic at
`t ∈ {7/2, 2, 5/2, 11/3, 3}`, `n = 1..7`, before the Lean proof was written. -/
theorem Aform_decomp (ht : 1 < t) (n : ℕ) :
    legQval t n + legVal t n * headSum t n
      = -(∑ j ∈ Finset.range (n + 1), (j : ℝ) * legCoef t n j)
        + (∑ r ∈ Finset.range (n - 1), legG t n ((t ^ (r + 1))⁻¹) / (t ^ (r + 1) - 1))
        + (∑ d ∈ Finset.range n, legTail t n (d + 1) * (t ^ (d + 1) / (t ^ (d + 1) - 1))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have ht0 := tpos ht
  -- (A) the flat double sum, reindexed by `d = j - i`
  have hflat := legQval_eq_flat ht (p + 1)
  have hreidx : ∀ j : ℕ, j ≤ p + 1 →
      (∑ i ∈ Finset.range j, legCoef t (p + 1) j
          * (((t : ℝ) ^ ((p + 1 - 1) * (j - i)))⁻¹ * ((t : ℝ) ^ (j - i) - 1)⁻¹))
        = ∑ i ∈ Finset.range j, legCoef t (p + 1) j
            * (((t : ℝ) ^ (p * (i + 1)))⁻¹ * ((t : ℝ) ^ (i + 1) - 1)⁻¹) := by
    intro j _
    refine Eq.trans ?_ (Finset.sum_range_reflect
      (fun i => legCoef t (p + 1) j
        * (((t : ℝ) ^ (p * (i + 1)))⁻¹ * ((t : ℝ) ^ (i + 1) - 1)⁻¹)) j)
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i < j := Finset.mem_range.mp hi
    rw [show p + 1 - 1 = p from rfl, show j - i = (j - 1 - i) + 1 from by omega]
  rw [Finset.sum_congr rfl (fun j hj =>
    hreidx j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))] at hflat
  -- (B) swap to `d`-outer form
  have hswap :
      (∑ j ∈ Finset.range (p + 1 + 1), ∑ i ∈ Finset.range j, legCoef t (p + 1) j
          * (((t : ℝ) ^ (p * (i + 1)))⁻¹ * ((t : ℝ) ^ (i + 1) - 1)⁻¹))
        = ∑ d ∈ Finset.range (p + 1),
            legTail t (p + 1) (d + 1)
              * (((t : ℝ) ^ (p * (d + 1)))⁻¹ * ((t : ℝ) ^ (d + 1) - 1)⁻¹) := by
    rw [Finset.sum_comm' (t' := Finset.range (p + 1))
      (s' := fun d => Finset.Icc (d + 1) (p + 1))
      (h := by
        intro j d
        simp only [Finset.mem_range, Finset.mem_Icc]
        omega)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [legTail, Finset.sum_mul]
  rw [hswap] at hflat
  -- (C) apply the partial fraction to each `d`
  have hgs : ∀ d ∈ Finset.range (p + 1),
      legTail t (p + 1) (d + 1)
          * (((t : ℝ) ^ (p * (d + 1)))⁻¹ * ((t : ℝ) ^ (d + 1) - 1)⁻¹)
        = legTail t (p + 1) (d + 1) * ((t : ℝ) ^ (d + 1) / ((t : ℝ) ^ (d + 1) - 1))
          - legTail t (p + 1) (d + 1)
              * ∑ r ∈ Finset.range (p + 1), ((t : ℝ) ^ (r * (d + 1)))⁻¹ := by
    intro d _
    have h := geom_split ht p (d := d + 1) (by omega)
    rw [← mul_sub]
    congr 1
    linarith [h]
  rw [Finset.sum_congr rfl hgs, Finset.sum_sub_distrib] at hflat
  -- (D) the geometric block, resummed over `r`
  have hblock :
      (∑ d ∈ Finset.range (p + 1), legTail t (p + 1) (d + 1)
          * ∑ r ∈ Finset.range (p + 1), ((t : ℝ) ^ (r * (d + 1)))⁻¹)
        = ∑ r ∈ Finset.range (p + 1),
            ∑ d ∈ Finset.range (p + 1),
              legTail t (p + 1) (d + 1) * ((t : ℝ) ^ ((d + 1) * r))⁻¹ := by
    have step1 : ∀ d : ℕ,
        legTail t (p + 1) (d + 1) * ∑ r ∈ Finset.range (p + 1), ((t : ℝ) ^ (r * (d + 1)))⁻¹
          = ∑ r ∈ Finset.range (p + 1),
              legTail t (p + 1) (d + 1) * ((t : ℝ) ^ ((d + 1) * r))⁻¹ := by
      intro d
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by rw [Nat.mul_comm (d + 1) r]
    rw [Finset.sum_congr rfl (fun d _ => step1 d), Finset.sum_comm]
  rw [hblock] at hflat
  -- (E) evaluate the `r`-blocks
  have hsplitr : (∑ r ∈ Finset.range (p + 1),
        ∑ d ∈ Finset.range (p + 1), legTail t (p + 1) (d + 1) * ((t : ℝ) ^ ((d + 1) * r))⁻¹)
      = (∑ r ∈ Finset.range p,
            ∑ d ∈ Finset.range (p + 1),
              legTail t (p + 1) (d + 1) * ((t : ℝ) ^ ((d + 1) * (r + 1)))⁻¹)
        + ∑ d ∈ Finset.range (p + 1),
            legTail t (p + 1) (d + 1) * ((t : ℝ) ^ ((d + 1) * 0))⁻¹ :=
    Finset.sum_range_succ' _ p
  rw [hsplitr] at hflat
  have hr0 : (∑ d ∈ Finset.range (p + 1),
        legTail t (p + 1) (d + 1) * ((t : ℝ) ^ ((d + 1) * 0))⁻¹)
      = ∑ j ∈ Finset.range (p + 1 + 1), (j : ℝ) * legCoef t (p + 1) j := by
    rw [← tail_sum_zero t (p + 1)]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp
  have hrpos : ∀ r ∈ Finset.range p,
      (∑ d ∈ Finset.range (p + 1),
          legTail t (p + 1) (d + 1) * ((t : ℝ) ^ ((d + 1) * (r + 1)))⁻¹)
        = (legVal t (p + 1) - legG t (p + 1) (((t : ℝ) ^ (r + 1))⁻¹))
            / ((t : ℝ) ^ (r + 1) - 1) := fun r _ => tail_sum_pos ht (p + 1) (by omega)
  rw [Finset.sum_congr rfl hrpos, hr0] at hflat
  -- (F) the head sum cancels the `legVal` half
  have hhead : legVal t (p + 1) * headSum t (p + 1)
      = ∑ r ∈ Finset.range p, legVal t (p + 1) / ((t : ℝ) ^ (r + 1) - 1) := by
    rw [headSum, Nat.add_sub_cancel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_one_div]
  have hsplitsum : (∑ r ∈ Finset.range p,
        (legVal t (p + 1) - legG t (p + 1) (((t : ℝ) ^ (r + 1))⁻¹))
          / ((t : ℝ) ^ (r + 1) - 1))
      = (∑ r ∈ Finset.range p, legVal t (p + 1) / ((t : ℝ) ^ (r + 1) - 1))
        - ∑ r ∈ Finset.range p,
            legG t (p + 1) (((t : ℝ) ^ (r + 1))⁻¹) / ((t : ℝ) ^ (r + 1) - 1) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [sub_div]
  rw [hsplitsum] at hflat
  rw [Nat.add_sub_cancel]
  rw [hflat, hhead]
  ring

end

end QHarm

#print axioms QHarm.geom_split
#print axioms QHarm.tail_sum_zero
#print axioms QHarm.tail_sum_pos
#print axioms QHarm.Aform_decomp
