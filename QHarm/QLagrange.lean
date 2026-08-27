/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QHarm.Orthogonality

/-!
# `QHarm/QLagrange.lean` — the little q-Legendre polynomial at the lattice points `t^m`

This is the identity that replaces Van Assche's equation (25): an explicit, manifestly
`t`-polynomial closed form for `P_n(t^{n-r})` with **no negative powers of `t` anywhere**,
so that the rational-track integrality count can be done term by term.

## Consumes

* `QHarm/QBinom.lean` — `gauss` (the real one-variable Gaussian binomial) and its definition
  as a product of `(t^a - 1)` quotients;
* `QHarm/Legendre.lean` — `legCoef`, `legG`, `legGamma`;
* `QHarm/Orthogonality.lean` — `Rfac` (the `t`-factorial) with `Rfac_split`, `Rfac_ne_zero`,
  the division-free product formula `gauss_mul_Rfac`, and `gauss_diag`.

Every statement below is proved outright.

## Method

The route is `Orthogonality`'s Lagrange/Cauchy picture with the nodes **reflected**: instead of
`q^j = t^{-j}` the interpolation nodes are `u_j = t^j`, `j = 0..n`, so every product is a
polynomial in `t` from the start.  Two ingredients, both elementary:

1. `legGamma_prod` — the `u`-side twin of `Orthogonality.lagrange_coef`.  Multiplying
   `γ_{n,j}` by the node `t^j` and by the Lagrange denominator `∏_{i≠j}(t^j - t^i)` leaves
   exactly `∏_{k<n} (1 - t^{k+j+1})`, with **no `j`-dependent scalar surviving**.  This is a
   closed-form product computation through `Rfac`, not a summation identity.
2. `dd_geom` — the divided difference of `X^d` at the geometric nodes `u_j = t^j` is `0` for
   `d < n` and the Gaussian binomial `[d,n]_t = h_{d-n}(1,t,…,t^n)` for `d ≥ n`.  It reduces
   through `node_prod` to Rothe's q-binomial theorem (`qbinom`), which in turn is a one-line
   induction on q-Pascal (`gauss_pascal`), itself a corollary of `gauss_mul_Rfac`.
   **No `Lagrange` API, no polynomial-degree argument, no power series.**

Expanding (1) by `qbinom` at `y = t^{j+1}`, exchanging the two finite sums and applying (2)
kills every term with `a < n - s` and leaves the target after a reflection `a ↦ n - a`.
The whole `t`-exponent bookkeeping collapses to `C(n+1,2) + C(a,2) = C(n+1-a,2) + n·a`,
handled subtraction-free by `omega` from `2·C(j,2) + j = j²`.

## Main results

* `legG_inv_pow` — **the target.**  For `1 < t` and `r < n`, with `s = n - 1 - r`,
  `legG t n ((t^r)⁻¹) = (-1)^n ∑_{a<n-r} (-1)^a [n,a]_t [n+s-a, s-a]_t t^{C(n+1-a,2)}`.
* `legG_eval_aux` — the same statement indexed by `s` instead of `r`.
* `dd_geom`, `dd_geom_lt`, `dd_geom_ge` — divided differences at geometric nodes.
* `qbinom` — Rothe's q-binomial theorem, `z` a free real (no ℕ-subtraction).
* `gauss_pascal` — q-Pascal `[n+1,a+1] = t^{a+1}[n,a+1] + [n,a]`, **valid only for `a < n`**
  (`gauss t n k = 1`, not `0`, for `k > n`).
* `gauss_symm` — `[n,j]_t = [n,n-j]_t`;  `Rfac_succ`;  `node_prod`;  `legGamma_prod`.

## What is NOT here

* Van Assche's `Q_n` and the Padé bridge — `QHarm/Forms.lean`, `QHarm/Pade.lean`;
* orthogonality and the squared norm — `QHarm/Orthogonality.lean`;
* integrality of the cleared forms — `QHarm/Integrality.lean`, `QHarm/RatIntegrality.lean`;
* any size bound on `legVal` or on the remainder — `QHarm/LegendreBounds.lean`.
-/

namespace QHarm

/-! ## Triangular-number bookkeeping -/

private theorem choose_two_succ' (k : ℕ) : (k + 1).choose 2 = k + k.choose 2 := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right]

private theorem two_choose_two_add' (j : ℕ) : 2 * j.choose 2 + j = j * j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h : 2 * (j + j.choose 2) + (j + 1) = (2 * j.choose 2 + j) + (2 * j + 1) := by ring
      rw [choose_two_succ', h, ih]
      ring

private theorem sum_range_id' (j : ℕ) : ∑ i ∈ Finset.range j, i = j.choose 2 := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, ih, choose_two_succ']; omega

/-! ## `Rfac` and `gauss` basics -/

theorem Rfac_succ (t : ℝ) (m : ℕ) : Rfac t (m + 1) = Rfac t m * (t ^ (m + 1) - 1) := by
  simp [Rfac, Finset.prod_range_succ]

/-- Symmetry of the Gaussian binomial. -/
theorem gauss_symm {t : ℝ} (ht : 1 < t) {n j : ℕ} (hj : j ≤ n) :
    gauss t n j = gauss t n (n - j) := by
  have h1 := gauss_mul_Rfac ht hj
  have h2 := gauss_mul_Rfac ht (Nat.sub_le n j)
  rw [show n - (n - j) = j from by omega] at h2
  have hne : Rfac t j * Rfac t (n - j) ≠ 0 :=
    mul_ne_zero (Rfac_ne_zero ht j) (Rfac_ne_zero ht (n - j))
  refine mul_right_cancel₀ hne ?_
  calc gauss t n j * (Rfac t j * Rfac t (n - j)) = Rfac t n := by linear_combination h1
    _ = gauss t n (n - j) * (Rfac t j * Rfac t (n - j)) := by linear_combination -h2

/-- **q-Pascal**, in the form used by the q-binomial theorem:
`[n+1, a+1] = t^{a+1} [n, a+1] + [n, a]`. -/
theorem gauss_pascal {t : ℝ} (ht : 1 < t) {n a : ℕ} (ha : a < n) :
    gauss t (n + 1) (a + 1) = t ^ (a + 1) * gauss t n (a + 1) + gauss t n a := by
  obtain ⟨m, rfl⟩ : ∃ m, n = a + 1 + m := ⟨n - (a + 1), by omega⟩
  have h1 : gauss t (a + 1 + m + 1) (a + 1) * Rfac t (a + 1) * Rfac t (m + 1)
      = Rfac t (a + 1 + m + 1) := by
    have h := gauss_mul_Rfac ht (show a + 1 ≤ a + 1 + m + 1 by omega)
    rwa [show a + 1 + m + 1 - (a + 1) = m + 1 from by omega] at h
  have h2 : gauss t (a + 1 + m) (a + 1) * Rfac t (a + 1) * Rfac t m = Rfac t (a + 1 + m) := by
    have h := gauss_mul_Rfac ht (show a + 1 ≤ a + 1 + m by omega)
    rwa [show a + 1 + m - (a + 1) = m from by omega] at h
  have h3 : gauss t (a + 1 + m) a * Rfac t a * Rfac t (m + 1) = Rfac t (a + 1 + m) := by
    have h := gauss_mul_Rfac ht (show a ≤ a + 1 + m by omega)
    rwa [show a + 1 + m - a = m + 1 from by omega] at h
  have hA : Rfac t (a + 1) = Rfac t a * (t ^ (a + 1) - 1) := Rfac_succ t a
  have hB : Rfac t (m + 1) = Rfac t m * (t ^ (m + 1) - 1) := Rfac_succ t m
  have hC : Rfac t (a + 1 + m + 1) = Rfac t (a + 1 + m) * (t ^ (a + 1 + m + 1) - 1) :=
    Rfac_succ t (a + 1 + m)
  have hpow : t ^ (a + 1) * t ^ (m + 1) = t ^ (a + 1 + m + 1) := by
    rw [← pow_add]; congr 1
  have hne : Rfac t (a + 1) * Rfac t (m + 1) ≠ 0 :=
    mul_ne_zero (Rfac_ne_zero ht (a + 1)) (Rfac_ne_zero ht (m + 1))
  refine mul_right_cancel₀ hne ?_
  have e1 : gauss t (a + 1 + m + 1) (a + 1) * (Rfac t (a + 1) * Rfac t (m + 1))
      = Rfac t (a + 1 + m) * (t ^ (a + 1 + m + 1) - 1) := by
    rw [← hC]; linear_combination h1
  have e2 : t ^ (a + 1) * gauss t (a + 1 + m) (a + 1) * (Rfac t (a + 1) * Rfac t (m + 1))
      = Rfac t (a + 1 + m) * (t ^ (a + 1) * (t ^ (m + 1) - 1)) := by
    rw [hB]; linear_combination (t ^ (a + 1) * (t ^ (m + 1) - 1)) * h2
  have e3 : gauss t (a + 1 + m) a * (Rfac t (a + 1) * Rfac t (m + 1))
      = Rfac t (a + 1 + m) * (t ^ (a + 1) - 1) := by
    rw [hA]; linear_combination (t ^ (a + 1) - 1) * h3
  rw [add_mul, e1, e2, e3]
  linear_combination Rfac t (a + 1 + m) * hpow

/-! ## The q-binomial theorem -/

/-- Pure bookkeeping: a sum over `range (n+2)` matches `(1 - y)` times a sum over `range (n+1)`
as soon as the three coefficient relations hold. -/
private theorem sum_shift_lemma (n : ℕ) (c d : ℕ → ℝ) (y : ℝ)
    (h0 : d 0 = c 0) (htop : d (n + 1) = -(c n * y))
    (hstep : ∀ a < n, d (a + 1) = c (a + 1) - c a * y) :
    ∑ a ∈ Finset.range (n + 2), d a = (∑ a ∈ Finset.range (n + 1), c a) * (1 - y) := by
  rw [Finset.sum_range_succ d (n + 1), Finset.sum_range_succ' d n, mul_sub, mul_one,
    Finset.sum_mul, Finset.sum_range_succ' c n, Finset.sum_range_succ (fun a => c a * y) n]
  have hcong : ∑ a ∈ Finset.range n, d (a + 1)
      = ∑ a ∈ Finset.range n, (c (a + 1) - c a * y) :=
    Finset.sum_congr rfl fun a ha => hstep a (Finset.mem_range.mp ha)
  rw [h0, htop, hcong, Finset.sum_sub_distrib]
  ring

/-- **Rothe's q-binomial theorem.**
`∏_{k<n} (1 - t^k y) = ∑_{a≤n} (-1)^a [n,a]_t t^{C(a,2)} y^a`. -/
theorem qbinom {t : ℝ} (ht : 1 < t) (n : ℕ) (y : ℝ) :
    ∑ a ∈ Finset.range (n + 1), (-1 : ℝ) ^ a * gauss t n a * t ^ (a.choose 2) * y ^ a
      = ∏ k ∈ Finset.range n, (1 - t ^ k * y) := by
  induction n generalizing y with
  | zero => simp [gauss]
  | succ n ih =>
      have hprod : ∏ k ∈ Finset.range (n + 1), (1 - t ^ k * y)
          = (∏ k ∈ Finset.range n, (1 - t ^ k * (t * y))) * (1 - y) := by
        rw [Finset.prod_range_succ' (fun k => 1 - t ^ k * y) n, pow_zero, one_mul]
        congr 1
        exact Finset.prod_congr rfl fun k _ => by ring
      rw [hprod, ← ih (t * y)]
      refine sum_shift_lemma n
        (fun a => (-1 : ℝ) ^ a * gauss t n a * t ^ (a.choose 2) * (t * y) ^ a)
        (fun a => (-1 : ℝ) ^ a * gauss t (n + 1) a * t ^ (a.choose 2) * y ^ a) y ?_ ?_ ?_
      · simp [gauss]
      · rw [gauss_diag ht (n + 1), gauss_diag ht n, choose_two_succ' n]
        ring
      · intro a ha
        rw [gauss_pascal ht ha, choose_two_succ' a]
        ring

/-! ## The node products at the geometric nodes `u_j = t^j` -/

/-- `∏_{i ≠ j, i ≤ n} (t^j - t^i)`, in closed form. -/
theorem node_prod {t : ℝ} {n j : ℕ} (hj : j ≤ n) :
    ∏ i ∈ (Finset.range (n + 1)).erase j, (t ^ j - t ^ i)
      = (-1) ^ (n - j) * t ^ (j.choose 2 + j * (n - j)) * (Rfac t j * Rfac t (n - j)) := by
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
  have hlow : ∏ i ∈ Finset.range j, (t ^ j - t ^ i) = t ^ (j.choose 2) * Rfac t j := by
    have hfac : ∀ i ∈ Finset.range j, (t ^ j - t ^ i) = t ^ i * (t ^ (j - 1 - i + 1) - 1) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      have hidx : j - 1 - i + 1 = j - i := by omega
      have hsum : t ^ i * t ^ (j - i) = t ^ j := by rw [← pow_add]; congr 1; omega
      rw [hidx]
      linear_combination -hsum
    simp only [Rfac]
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      sum_range_id', Finset.prod_range_reflect (fun i => t ^ (i + 1) - 1) j]
  have hhigh : ∏ i ∈ Finset.Ico (j + 1) (n + 1), (t ^ j - t ^ i)
      = (-1) ^ (n - j) * t ^ (j * (n - j)) * Rfac t (n - j) := by
    rw [Finset.prod_Ico_eq_prod_range, show n + 1 - (j + 1) = n - j from by omega]
    have hfac : ∀ u ∈ Finset.range (n - j),
        (t ^ j - t ^ (j + 1 + u)) = (-(t ^ j)) * (t ^ (u + 1) - 1) := by
      intro u _
      have hsum : t ^ j * t ^ (u + 1) = t ^ (j + 1 + u) := by rw [← pow_add]; congr 1; omega
      linear_combination hsum
    simp only [Rfac]
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range, neg_pow, ← pow_mul]
  rw [hsplit, Finset.prod_union hdisj, hlow, hhigh, pow_add]
  ring

/-- **The Lagrange coefficient at the geometric nodes.**  This is the `u`-side twin of
`Orthogonality.lagrange_coef`: the little q-Legendre coefficient `γ_{n,j}`, multiplied by the
node `t^j` and by the Lagrange denominator, collapses to the polynomial
`∏_{k<n} (1 - t^{k+j+1})` — no `j`-dependent scalar left over. -/
theorem legGamma_prod {t : ℝ} (ht : 1 < t) {n j : ℕ} (hj : j ≤ n) :
    legGamma t n j * t ^ j * (∏ i ∈ (Finset.range (n + 1)).erase j, (t ^ j - t ^ i))
      = ∏ k ∈ Finset.range n, (1 - t ^ (k + j + 1)) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt ht0
  have hgp : gauss t n j * gauss t (n + j) n * (Rfac t j * Rfac t j * Rfac t (n - j))
      = Rfac t (n + j) := by
    have h1 := gauss_mul_Rfac ht hj
    have h2 := gauss_mul_Rfac ht (Nat.le_add_right n j)
    rw [show n + j - n = j from by omega] at h2
    linear_combination (gauss t (n + j) n * Rfac t j) * h1 + h2
  have hexp : j.choose 2 + j + (j.choose 2 + j * (n - j)) = n * j := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [show j + d - j = d from by omega]
    have h := two_choose_two_add' j
    have hm : j * d = d * j := Nat.mul_comm j d
    have hq : (j + d) * j = j * j + d * j := by ring
    omega
  have hsign : ((-1 : ℝ)) ^ j * (-1) ^ (n - j) = (-1) ^ n := by
    rw [← pow_add, show j + (n - j) = n from by omega]
  have hpowinv : t ^ (j.choose 2) * t ^ j * t ^ (j.choose 2 + j * (n - j)) * ((t ^ n) ^ j)⁻¹
      = 1 := by
    rw [← pow_add, ← pow_add, hexp, ← pow_mul]
    exact mul_inv_cancel₀ (pow_ne_zero _ htne)
  have hL : legGamma t n j * t ^ j
        * (∏ i ∈ (Finset.range (n + 1)).erase j, (t ^ j - t ^ i)) * Rfac t j
      = (-1) ^ n * Rfac t (n + j) := by
    have hbig : legGamma t n j * t ^ j
          * (∏ i ∈ (Finset.range (n + 1)).erase j, (t ^ j - t ^ i)) * Rfac t j
        = ((-1 : ℝ) ^ j * (-1) ^ (n - j))
            * (t ^ (j.choose 2) * t ^ j * t ^ (j.choose 2 + j * (n - j)) * ((t ^ n) ^ j)⁻¹)
            * (gauss t n j * gauss t (n + j) n * (Rfac t j * Rfac t j * Rfac t (n - j))) := by
      rw [node_prod hj, legGamma, legCoef]; ring
    rw [hbig, hsign, hpowinv, hgp]
    ring
  have hR : (∏ k ∈ Finset.range n, (1 - t ^ (k + j + 1))) * Rfac t j
      = (-1) ^ n * Rfac t (n + j) := by
    have hfac : ∀ k ∈ Finset.range n,
        (1 - t ^ (k + j + 1)) = (-1) * (t ^ (j + k + 1) - 1) := by
      intro k _
      rw [show k + j + 1 = j + k + 1 from by omega]; ring
    have hs := Rfac_split t j n
    rw [show j + n = n + j from by omega] at hs
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range, hs]
    ring
  exact mul_right_cancel₀ (Rfac_ne_zero ht j) (hL.trans hR.symm)

/-! ## Divided differences at the geometric nodes -/

/-- The divided-difference sum, multiplied by `[n]_t!`, is a q-binomial product. -/
private theorem dd_key {t : ℝ} (ht : 1 < t) (n d : ℕ) :
    Rfac t n * ∑ j ∈ Finset.range (n + 1),
        (t ^ j) ^ d / ∏ i ∈ (Finset.range (n + 1)).erase j, (t ^ j - t ^ i)
      = (-1) ^ n * ∏ k ∈ Finset.range n, (1 - t ^ k * (t ^ (d + 1) * (t ^ n)⁻¹)) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt ht0
  have hterm : ∀ j ∈ Finset.range (n + 1),
      Rfac t n * ((t ^ j) ^ d / ∏ i ∈ (Finset.range (n + 1)).erase j, (t ^ j - t ^ i))
        = (-1) ^ n * ((-1 : ℝ) ^ j * gauss t n j * t ^ (j.choose 2)
            * (t ^ (d + 1) * (t ^ n)⁻¹) ^ j) := by
    intro j hjm
    have hjn : j ≤ n := by have := Finset.mem_range.mp hjm; omega
    have hB := node_prod (t := t) hjn
    have hBne : (∏ i ∈ (Finset.range (n + 1)).erase j, (t ^ j - t ^ i)) ≠ 0 := by
      rw [hB]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ htne))
        (mul_ne_zero (Rfac_ne_zero ht j) (Rfac_ne_zero ht (n - j)))
    have hgm := gauss_mul_Rfac ht hjn
    have hs2 : ((-1 : ℝ)) ^ n * ((-1) ^ j * (-1) ^ (n - j)) = 1 := by
      rw [← pow_add, show j + (n - j) = n from by omega, ← pow_add]
      norm_num
    have hE : j.choose 2 + (j.choose 2 + j * (n - j)) + (d + 1) * j = j * d + n * j := by
      obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hjn
      rw [show j + b - j = b from by omega]
      have h := two_choose_two_add' j
      have h1 : (d + 1) * j = d * j + j := by ring
      have h2 : (j + b) * j = j * j + b * j := by ring
      have h3 : j * b = b * j := Nat.mul_comm j b
      have h4 : j * d = d * j := Nat.mul_comm j d
      omega
    have hpw : t ^ (j.choose 2) * t ^ (j.choose 2 + j * (n - j)) * (t ^ (d + 1)) ^ j
        = (t ^ j) ^ d * (t ^ n) ^ j := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add, hE]
    have hinv : ((t ^ n) ^ j)⁻¹ * (t ^ n) ^ j = 1 :=
      inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ htne))
    rw [← mul_div_assoc, div_eq_iff hBne, hB]
    have hrw : ((-1 : ℝ) ^ n * ((-1 : ℝ) ^ j * gauss t n j * t ^ (j.choose 2)
            * (t ^ (d + 1) * (t ^ n)⁻¹) ^ j))
          * ((-1 : ℝ) ^ (n - j) * t ^ (j.choose 2 + j * (n - j))
              * (Rfac t j * Rfac t (n - j)))
        = ((-1 : ℝ) ^ n * ((-1 : ℝ) ^ j * (-1 : ℝ) ^ (n - j)))
            * (t ^ (j.choose 2) * t ^ (j.choose 2 + j * (n - j)) * (t ^ (d + 1)) ^ j)
            * (((t ^ n) ^ j)⁻¹)
            * (gauss t n j * Rfac t j * Rfac t (n - j)) := by
      rw [mul_pow, inv_pow]; ring
    rw [hrw, hs2, hpw, hgm]
    linear_combination (-(Rfac t n * (t ^ j) ^ d)) * hinv
  rw [Finset.mul_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    qbinom ht n (t ^ (d + 1) * (t ^ n)⁻¹)]

/-- **Divided differences at geometric nodes, vanishing branch.** -/
theorem dd_geom_lt {t : ℝ} (ht : 1 < t) {n d : ℕ} (hd : d < n) :
    ∑ j ∈ Finset.range (n + 1),
        (t ^ j) ^ d / ∏ i ∈ (Finset.range (n + 1)).erase j, ((t : ℝ) ^ j - t ^ i) = 0 := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt ht0
  have h := dd_key ht n d
  have hzero : ∏ k ∈ Finset.range n, (1 - t ^ k * (t ^ (d + 1) * (t ^ n)⁻¹)) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_range.mpr (show n - 1 - d < n by omega)) ?_
    have hpow : t ^ (n - 1 - d) * t ^ (d + 1) = t ^ n := by
      rw [← pow_add]; congr 1; omega
    have hone : t ^ (n - 1 - d) * (t ^ (d + 1) * (t ^ n)⁻¹) = 1 := by
      rw [← mul_assoc, hpow]
      exact mul_inv_cancel₀ (pow_ne_zero _ htne)
    rw [hone]; ring
  rw [hzero, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (Rfac_ne_zero ht n)

/-- **Divided differences at geometric nodes, evaluating branch.** -/
theorem dd_geom_ge {t : ℝ} (ht : 1 < t) {n d : ℕ} (hd : n ≤ d) :
    ∑ j ∈ Finset.range (n + 1),
        (t ^ j) ^ d / ∏ i ∈ (Finset.range (n + 1)).erase j, ((t : ℝ) ^ j - t ^ i)
      = gauss t d n := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt ht0
  have h := dd_key ht n d
  have hg : gauss t d n * Rfac t n = ∏ k ∈ Finset.range n, (t ^ (d - n + k + 1) - 1) := by
    have h1 := gauss_mul_Rfac ht hd
    have h2 := Rfac_split t (d - n) n
    rw [show d - n + n = d from by omega] at h2
    rw [h2] at h1
    exact mul_right_cancel₀ (Rfac_ne_zero ht (d - n)) (by linear_combination h1)
  have hprod : ∏ k ∈ Finset.range n, (1 - t ^ k * (t ^ (d + 1) * (t ^ n)⁻¹))
      = (-1) ^ n * (gauss t d n * Rfac t n) := by
    have hinv : ((t : ℝ) ^ n)⁻¹ * t ^ n = 1 := inv_mul_cancel₀ (pow_ne_zero _ htne)
    have hfac : ∀ k ∈ Finset.range n,
        (1 - t ^ k * (t ^ (d + 1) * (t ^ n)⁻¹)) = (-1) * (t ^ (d - n + k + 1) - 1) := by
      intro k _
      have hpow : t ^ (d - n + k + 1) * t ^ n = t ^ k * t ^ (d + 1) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      linear_combination ((t : ℝ) ^ n)⁻¹ * hpow - t ^ (d - n + k + 1) * hinv
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range, hg]
  have hu : ((-1 : ℝ)) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [hprod] at h
  refine mul_left_cancel₀ (Rfac_ne_zero ht n) ?_
  linear_combination h + (gauss t d n * Rfac t n) * hu

/-- **Divided differences at geometric nodes.**  For the nodes `u_j = t^j`, `j = 0..n`,
the divided difference of `X^d` is `0` below the degree threshold and the Gaussian binomial
`[d, n]_t = h_{d-n}(1, t, …, t^n)` above it. -/
theorem dd_geom {t : ℝ} (ht : 1 < t) (n d : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
        (t ^ j) ^ d / ∏ i ∈ (Finset.range (n + 1)).erase j, ((t : ℝ) ^ j - t ^ i)
      = if d < n then 0 else gauss t d n := by
  by_cases h : d < n
  · rw [if_pos h]; exact dd_geom_lt ht h
  · rw [if_neg h]; exact dd_geom_ge ht (by omega)

/-! ## The closed form of `P_n` at the lattice points -/

/-- Reflect a `range (n+1)` sum and truncate it to `range (s+1)` when the reflected summand
vanishes above `s`. -/
private theorem sum_reflect_trunc (n s : ℕ) (f : ℕ → ℝ) (hsn : s < n)
    (hvan : ∀ b, s < b → b ≤ n → f (n - b) = 0) :
    ∑ a ∈ Finset.range (n + 1), f a = ∑ b ∈ Finset.range (s + 1), f (n - b) := by
  rw [← Finset.sum_range_reflect f (n + 1)]
  simp only [Nat.add_sub_cancel]
  have hsub : Finset.range (s + 1) ⊆ Finset.range (n + 1) := by
    intro x hx
    have := Finset.mem_range.mp hx
    exact Finset.mem_range.mpr (by omega)
  refine (Finset.sum_subset hsub ?_).symm
  intro b hb hnb
  have h1 : b ≤ n := by have := Finset.mem_range.mp hb; omega
  have h2 : s < b := by
    by_contra hc
    exact hnb (Finset.mem_range.mpr (by omega))
  exact hvan b h2 h1

/-- **The little q-Legendre polynomial at the points `t^m`, in closed form.**
For `1 < t` and `r < n`, writing `s = n - 1 - r` (so the evaluation point is `P_n(t^{n-r})`). -/
theorem legG_inv_pow {t : ℝ} (ht : 1 < t) {n r : ℕ} (hr : r < n) :
    legG t n ((t ^ r)⁻¹)
      = (-1) ^ n * ∑ a ∈ Finset.range (n - r),
          (-1) ^ a * gauss t n a * gauss t (n + (n - 1 - r) - a) ((n - 1 - r) - a)
            * t ^ ((n + 1 - a).choose 2) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt ht0
  obtain ⟨s, hsdef⟩ : ∃ s, s = n - 1 - r := ⟨n - 1 - r, rfl⟩
  have hrs : r + s + 1 = n := by omega
  have hsn : s < n := by omega
  rw [← hsdef, show n - r = s + 1 from by omega]
  -- Steps 1-3: reflect the nodes and expand by the q-binomial theorem.
  have hLHS : legG t n ((t ^ r)⁻¹)
      = ∑ j ∈ Finset.range (n + 1),
          ∑ a ∈ Finset.range (n + 1),
            ((-1 : ℝ) ^ a * gauss t n a * t ^ (a.choose 2) * t ^ a)
              * ((t ^ j) ^ (s + a)
                  / ∏ i ∈ (Finset.range (n + 1)).erase j, (t ^ j - t ^ i)) := by
    rw [legG]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
    have hne2 : ((t : ℝ) ^ n) ^ j ≠ 0 := pow_ne_zero _ (pow_ne_zero _ htne)
    have hBne : (∏ i ∈ (Finset.range (n + 1)).erase j, (t ^ j - t ^ i)) ≠ 0 := by
      rw [node_prod hjn]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ htne))
        (mul_ne_zero (Rfac_ne_zero ht j) (Rfac_ne_zero ht (n - j)))
    have hpm : ((t : ℝ) ^ r) ^ j * ((t : ℝ) ^ j) ^ (s + 1) = ((t : ℝ) ^ n) ^ j := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      rw [show r * j + j * (s + 1) = (r + s + 1) * j from by ring, hrs]
    have e0 : (((t : ℝ) ^ r)⁻¹) ^ j = (((t : ℝ) ^ n) ^ j)⁻¹ * ((t : ℝ) ^ j) ^ (s + 1) := by
      rw [inv_pow]
      refine inv_eq_of_mul_eq_one_right ?_
      calc ((t : ℝ) ^ r) ^ j * ((((t : ℝ) ^ n) ^ j)⁻¹ * ((t : ℝ) ^ j) ^ (s + 1))
          = (((t : ℝ) ^ n) ^ j)⁻¹ * (((t : ℝ) ^ r) ^ j * ((t : ℝ) ^ j) ^ (s + 1)) := by ring
        _ = 1 := by rw [hpm]; exact inv_mul_cancel₀ hne2
    have e1 : legCoef t n j * (((t : ℝ) ^ r)⁻¹) ^ j
        = ((t : ℝ) ^ j) ^ s * (legGamma t n j * t ^ j) := by
      rw [legGamma, e0, pow_succ]; ring
    have e2 : legGamma t n j * t ^ j
        = (∏ k ∈ Finset.range n, (1 - t ^ (k + j + 1)))
            / ∏ i ∈ (Finset.range (n + 1)).erase j, (t ^ j - t ^ i) := by
      rw [eq_div_iff hBne]
      exact legGamma_prod ht hjn
    have e3 : (∏ k ∈ Finset.range n, (1 - t ^ (k + j + 1)))
        = ∑ a ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ a * gauss t n a * t ^ (a.choose 2) * ((t : ℝ) ^ (j + 1)) ^ a := by
      rw [qbinom ht n ((t : ℝ) ^ (j + 1))]
      exact Finset.prod_congr rfl fun k _ => by
        rw [show k + j + 1 = k + (j + 1) from by omega, pow_add]
    rw [e1, e2, e3, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hp1 : ((t : ℝ) ^ (j + 1)) ^ a = ((t : ℝ) ^ j) ^ a * t ^ a := by
      rw [← mul_pow, ← pow_succ]
    have hnum : ((t : ℝ) ^ j) ^ s
          * ((-1 : ℝ) ^ a * gauss t n a * t ^ (a.choose 2) * ((t : ℝ) ^ (j + 1)) ^ a)
        = ((-1 : ℝ) ^ a * gauss t n a * t ^ (a.choose 2) * t ^ a)
            * ((t : ℝ) ^ j) ^ (s + a) := by
      rw [hp1, pow_add]; ring
    rw [← mul_div_assoc, ← mul_div_assoc, hnum]
  rw [hLHS, Finset.sum_comm]
  -- Step 4: the inner sums are divided differences.
  have hdd : ∀ a ∈ Finset.range (n + 1),
      (∑ j ∈ Finset.range (n + 1),
          ((-1 : ℝ) ^ a * gauss t n a * t ^ (a.choose 2) * t ^ a)
            * ((t ^ j) ^ (s + a)
                / ∏ i ∈ (Finset.range (n + 1)).erase j, (t ^ j - t ^ i)))
        = ((-1 : ℝ) ^ a * gauss t n a * t ^ (a.choose 2) * t ^ a)
            * (if s + a < n then 0 else gauss t (s + a) n) := by
    intro a _
    rw [← Finset.mul_sum, dd_geom ht n (s + a)]
  rw [Finset.sum_congr rfl hdd]
  -- Step 5: reflect `a ↦ n - a` and truncate.
  refine (sum_reflect_trunc n s _ hsn ?_).trans ?_
  · intro b hb1 hb2
    rw [if_pos (show s + (n - b) < n by omega), mul_zero]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbs : b ≤ s := by have := Finset.mem_range.mp hb; omega
    rw [if_neg (show ¬ (s + (n - b) < n) by omega)]
    have hg1 : gauss t n (n - b) = gauss t n b := (gauss_symm ht (show b ≤ n by omega)).symm
    have hg2 : gauss t (s + (n - b)) n = gauss t (n + s - b) (s - b) := by
      rw [show s + (n - b) = n + s - b from by omega,
        gauss_symm ht (show n ≤ n + s - b by omega),
        show n + s - b - n = s - b from by omega]
    have hpow : (t : ℝ) ^ ((n - b).choose 2) * t ^ (n - b) = t ^ ((n + 1 - b).choose 2) := by
      rw [← pow_add, show n + 1 - b = (n - b) + 1 from by omega, choose_two_succ']
      congr 1
      omega
    have hsign : ((-1 : ℝ)) ^ (n - b) = (-1) ^ n * (-1) ^ b := by
      rw [← pow_add, show n + b = (n - b) + 2 * b from by omega, pow_add, pow_mul]
      norm_num
    rw [hg1, hg2, hsign]
    linear_combination
      ((-1 : ℝ) ^ n * (-1) ^ b * gauss t n b * gauss t (n + s - b) (s - b)) * hpow

/-- `legG_inv_pow` re-indexed by `s = n - 1 - r`, the shape in which the exponent count is
usually read: the evaluation point is `P_n(t^{s+1})`. -/
theorem legG_eval_aux {t : ℝ} (ht : 1 < t) {n s : ℕ} (hs : s < n) :
    legG t n ((t ^ (n - 1 - s))⁻¹)
      = (-1) ^ n * ∑ a ∈ Finset.range (s + 1),
          (-1) ^ a * gauss t n a * gauss t (n + s - a) (s - a)
            * t ^ ((n + 1 - a).choose 2) := by
  have h := legG_inv_pow ht (show n - 1 - s < n by omega)
  rwa [show n - 1 - (n - 1 - s) = s from by omega,
    show n - (n - 1 - s) = s + 1 from by omega] at h

#print axioms QHarm.legG_inv_pow
#print axioms QHarm.legG_eval_aux
#print axioms QHarm.dd_geom
#print axioms QHarm.qbinom
#print axioms QHarm.gauss_pascal
#print axioms QHarm.legGamma_prod

end QHarm
