/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QHarm.Forms

/-!
# `QHarm/LegendreBounds.lean` — dominant-term separation in (23), and the sharp remainder

**Status note.** the internal build notes deviation **D2** deleted this file: the *integer* track
(`irrational_int`, Erdős 1948) needs no information at all about the size of `P_n(t^n)`,
because the lossy remainder bound `|R_n| ≤ C·t^{-n²-n}` obtained by truncating a geometric
expansion (`QHarm/Forms.lean`'s `abs_rem_le`) already beats the crude clearing.  It is
**reinstated for the rational track only**: there the crude bound yields only `θ < 0.278`,
whereas `irrational_half_odd` needs `θ = 0.3562` and the general theorem `θ < 1/2 − 1/π²`.
The sharp route replaces the truncation by the sum-of-squares identity, which trades the
lossy `t^{-n²}` for the *exact* squared norm divided by `|P_n(t^n)| ≈ t^{3n²/2}` — and that
requires a genuine **lower** bound on `|P_n(t^n)|`, which is what this file supplies.

## Consumes

* `QHarm/QBinom.lean` — `gauss`, `pow_le_gauss`, `gauss_le_const_mul_pow`, `gaussConst`,
  `one_le_gaussConst`;
* `QHarm/Legendre.lean` — `legCoef`, `legVal`, `legVal_eq`, `latVal`;
* `QHarm/CoefBound.lean` — `gammaExp`, `abs_legCoef_le_aux`, `two_mul_choose_two_add`,
  `summable_weight_sq_latVal`;
* `QHarm/Orthogonality.lean` — `norm_sq_value` (the squared norm, **exactly**);
* `QHarm/Pade.lean` — `rem`, `pade_den_pos`;
* `QHarm/Forms.lean` — `sumsq` (Van Assche (34)), `sumsq_pos`, `summable_sq`, `latVal_def`.

**There are no frontiers in this file.**  Every dependency listed above is `sorry`-free and
on disk, so every statement below is proved outright.

## Main results

* `degTerm n j = C(j,2) + j(n−j) + nj` — the `t`-degree of the `j`-th term of Van Assche
  (23), i.e. `gammaExp n j + n*j`.  `degTerm n n = C(n,2) + n²`, which is `n(3n−1)/2`
  (subtraction-free form: `2·degTerm n n + n = 3n²`, `two_mul_degTerm_diag`).
* `degTerm_add_gap` — the **exact** separation identity, in ℕ and subtraction-free:
  `degTerm n j + ((n−j)·n + C(n−j,2)) = degTerm n n` for `j ≤ n`.
  Consecutive gaps are therefore `degTerm n (j+1) − degTerm n j = 2n − j − 1 ≥ n`
  (`degTerm_succ_sub`); the original sketch said `≥ n − 1`, which is true but not
  sharp — the correct bound on the range that matters is `≥ n`.
* `abs_head_le` — the head `∑_{j<n} legCoef t n j` of (23) is at most **half** the dominant
  term, `≤ t^{degTerm n n}/2`.
* `legVal_lower` — `t^{degTerm n n}/2 ≤ |legVal t n|`.
* `legVal_sign` — `0 < (−1)^n · legVal t n`; and `legVal_ne_zero`.
* `abs_rem_le_sharp` — the sharp remainder bound,
  `|rem t n| ≤ (2 t^{n+1} / ((t^n − 1)(t^{2n+1} − 1))) / t^{degTerm n n}`.

## The largeness hypothesis

Everything from `abs_head_le` on carries **`hn : 4 * gaussConst t ^ 2 ≤ t ^ n`** together
with `ht : 2 ≤ t`.  This is an eventual condition (`gaussConst t = exp (t/(t−1)²)` depends
on neither `n` nor `j`, so `t^n → ∞` clears it), which is all the downstream assembly needs;
`∀ᶠ n in atTop` follows from `tendsto_pow_atTop_atTop_of_one_lt`.  It also *implies* `1 ≤ n`
(`one_le_of_threshold`), so no separate `1 ≤ n` hypothesis is carried.

Numerically the condition is `n ≥ 8` at `t = 2`, `n ≥ 3` at `t = 3`, `n ≥ 2` at `t = 5`,
`n ≥ 1` at `t = 7`.  The truth is far better — measured `|head|/|dominant|` is already
`0.333` at `t = 2, n = 1` — but nothing downstream is tight (the internal build notes, "Verified
numerics"), so no effort is spent sharpening it.

## What is NOT here

* the orthogonality relations and the squared norm — `QHarm/Orthogonality.lean`;
* the sum-of-squares identity (34) itself and the *lossy* remainder bound used by the
  integer track — `QHarm/Forms.lean`;
* the clearing factors, crude or cyclotomic — `QHarm/Clearing.lean`, `QHarm/Cyclotomic.lean`;
* the growth `𝒟_n^{1/n²} → P^{3/π²}` — `QHarm/Growth.lean`;
* integrality of the cleared rational forms — `QHarm/RatIntegrality.lean`;
* the assembly into `master_rat` — `QHarm/MainRat.lean`.
-/

namespace QHarm

open Finset

/-! ### The degree count of Van Assche (23)

`legCoef t n j = (-1)^j t^{C(j,2)} [n,j]_t [n+j,n]_t`, and `QHarm/QBinom.lean` pins each
Gaussian binomial two-sidedly: `t^{j(n-j)} ≤ [n,j]_t ≤ C·t^{j(n-j)}` and
`t^{nj} ≤ [n+j,n]_t ≤ C·t^{nj}` with `C = gaussConst t` independent of `n` and `j`.  So the
`j`-th term of (23) has `t`-degree `degTerm n j` up to the factor `C²`. -/

/-- The `t`-degree of the `j`-th term of Van Assche (23). -/
def degTerm (n j : ℕ) : ℕ := j.choose 2 + j * (n - j) + n * j

theorem degTerm_eq_gammaExp_add (n j : ℕ) : degTerm n j = gammaExp n j + n * j := rfl

@[simp] theorem degTerm_zero_right (n : ℕ) : degTerm n 0 = 0 := by simp [degTerm]

theorem degTerm_diag (n : ℕ) : degTerm n n = n.choose 2 + n * n := by
  simp [degTerm]

/-- `degTerm n n = n(3n−1)/2`, subtraction- and division-free.  This is the exponent the
manuscript calls `C_n`, and the internal build notes records that the measured minimal integralising
exponent equals it exactly. -/
theorem two_mul_degTerm_diag (n : ℕ) : 2 * degTerm n n + n = 3 * (n * n) := by
  have h := two_mul_choose_two_add n
  rw [degTerm_diag]
  omega

/-- Vandermonde at `k = 2`: `C(j+m,2) = C(j,2) + jm + C(m,2)`. -/
private theorem choose_two_add (j m : ℕ) :
    (j + m).choose 2 = j.choose 2 + j * m + m.choose 2 := by
  have hA := two_mul_choose_two_add j
  have hB := two_mul_choose_two_add m
  have hC := two_mul_choose_two_add (j + m)
  have hexp : (j + m) * (j + m) = j * j + 2 * (j * m) + m * m := by ring
  omega

/-- **The separation identity, exactly.**  For `j ≤ n`,

    degTerm n n − degTerm n j  =  (n − j)·n + C(n − j, 2),

written additively so that no ℕ-subtraction appears on the large side.  Equality of the
`(n−j)·n` part with the naive "gap ≥ n at every step" count is why the geometric factor
below is a plain `∑ u^i` with ratio `u = t^{-n}`. -/
theorem degTerm_add_gap {n j : ℕ} (h : j ≤ n) :
    degTerm n j + ((n - j) * n + (n - j).choose 2) = degTerm n n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have hsub : j + m - j = m := by omega
  have hself : j + m - (j + m) = 0 := by omega
  simp only [degTerm, hsub, hself]
  rw [choose_two_add]
  ring

/-- The consequence actually used: each non-dominant term is below the dominant one by at
least `(n − j)` full powers of `t^n`. -/
theorem degTerm_add_mul_le {n j : ℕ} (h : j ≤ n) :
    degTerm n j + n * (n - j) ≤ degTerm n n := by
  have hg := degTerm_add_gap h
  have hc : (n - j) * n = n * (n - j) := Nat.mul_comm _ _
  omega

/-- The consecutive gap, for the record: `degTerm n (j+1) − degTerm n j = 2n − j − 1`, hence
`≥ n` for every `j < n`.  (The campaign sketch said `≥ n − 1`; the sharp value on the range
that matters is `≥ n`, and the proofs below use the stronger `degTerm_add_mul_le` form.) -/
theorem degTerm_succ_sub {n j : ℕ} (h : j < n) :
    degTerm n j + (2 * n - j - 1) = degTerm n (j + 1) := by
  have h1 := degTerm_add_gap (le_of_lt h)
  have h2 := degTerm_add_gap (n := n) (j := j + 1) (by omega)
  have hA : 2 * (n - j).choose 2 + (n - j) = (n - j) * (n - j) := two_mul_choose_two_add (n - j)
  have hB : 2 * (n - (j + 1)).choose 2 + (n - (j + 1)) = (n - (j + 1)) * (n - (j + 1)) :=
    two_mul_choose_two_add (n - (j + 1))
  have hC : (n - j) * (n - j) = (n - (j + 1)) * (n - (j + 1)) + 2 * (n - (j + 1)) + 1 := by
    obtain ⟨d, hd⟩ : ∃ d, n - j = d + 1 := ⟨n - j - 1, by omega⟩
    have : n - (j + 1) = d := by omega
    rw [hd, this]; ring
  have hD : (n - j) * n = (n - (j + 1)) * n + n := by
    obtain ⟨d, hd⟩ : ∃ d, n - j = d + 1 := ⟨n - j - 1, by omega⟩
    have : n - (j + 1) = d := by omega
    rw [hd, this]; ring
  omega

/-! ### Elementary analytic scaffolding

`QHarm/QBinom.lean` proves the finite geometric bound as a `private` lemma, so it is
restated here rather than imported. -/

private theorem geom_sum_le_inv' {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (k : ℕ) :
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

/-- `∑_{j<n} u^{n-j} ≤ 2u` for `0 ≤ u ≤ 1/2` — the reversed geometric tail. -/
private theorem sum_pow_sub_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) (n : ℕ) :
    ∑ j ∈ Finset.range n, u ^ (n - j) ≤ 2 * u := by
  have hrefl : ∑ j ∈ Finset.range n, u ^ (n - j) = ∑ j ∈ Finset.range n, u ^ (j + 1) :=
    Eq.trans
      (Finset.sum_congr rfl (fun j hj => by
        have hj' := Finset.mem_range.mp hj
        congr 1
        omega))
      (Finset.sum_range_reflect (fun j => u ^ (j + 1)) n)
  have hfac : ∑ j ∈ Finset.range n, u ^ (j + 1) = u * ∑ j ∈ Finset.range n, u ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hgeo : ∑ j ∈ Finset.range n, u ^ j ≤ 1 / (1 - u) :=
    geom_sum_le_inv' h0 (by linarith) n
  have h2 : (1 : ℝ) / (1 - u) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  rw [hrefl, hfac]
  calc u * ∑ j ∈ Finset.range n, u ^ j ≤ u * 2 :=
        mul_le_mul_of_nonneg_left (le_trans hgeo h2) h0
    _ = 2 * u := by ring

/-! ### The two-sided bounds on the terms of (23) -/

/-- Every term of (23) is at most `gaussConst² t^{degTerm n j}` in absolute value.  This is
`QHarm/CoefBound.lean`'s `abs_legCoef_le_aux` repackaged in `degTerm` shape. -/
theorem abs_legCoef_le_degTerm {t : ℝ} (ht : 1 < t) {n j : ℕ} (h : j ≤ n) :
    |legCoef t n j| ≤ gaussConst t ^ 2 * t ^ degTerm n j := by
  refine le_trans (abs_legCoef_le_aux ht h) (le_of_eq ?_)
  rw [degTerm_eq_gammaExp_add, pow_add]

/-- **The dominant term.**  `(-1)^n · legCoef t n n ≥ t^{degTerm n n}`, with no constant:
the two Gaussian binomials involved are `[n,n]_t = 1` and `[2n,n]_t ≥ t^{n²}`. -/
theorem pow_degTerm_le_signed_diag {t : ℝ} (ht : 1 < t) (n : ℕ) :
    t ^ degTerm n n ≤ (-1) ^ n * legCoef t n n := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have h1 : (1 : ℝ) ≤ gauss t n n := by
    have h := pow_le_gauss ht (le_refl n)
    simpa using h
  have h2 : t ^ (n * n) ≤ gauss t (n + n) n := by
    have h := pow_le_gauss ht (Nat.le_add_right n n)
    rwa [Nat.add_sub_cancel_left] at h
  have hu : ((-1 : ℝ)) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hsign : (-1 : ℝ) ^ n * legCoef t n n
      = t ^ (n.choose 2) * gauss t n n * gauss t (n + n) n := by
    unfold legCoef
    linear_combination (t ^ (n.choose 2) * gauss t n n * gauss t (n + n) n) * hu
  rw [hsign]
  have hA : (0 : ℝ) < t ^ (n.choose 2) := pow_pos ht0 _
  have hb : (0 : ℝ) ≤ t ^ (n.choose 2) * gauss t n n :=
    mul_nonneg hA.le (le_trans zero_le_one h1)
  calc t ^ degTerm n n = t ^ (n.choose 2) * 1 * t ^ (n * n) := by
        rw [degTerm_diag, pow_add]; ring
    _ ≤ t ^ (n.choose 2) * gauss t n n * gauss t (n + n) n :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hA.le) h2 (pow_pos ht0 _).le hb

/-! ### The largeness hypothesis -/

/-- `4 gaussConst t ^ 2 ≤ t ^ n` forces `n ≥ 1`, since `gaussConst t ≥ 1` and `t^0 = 1`. -/
theorem one_le_of_threshold {t : ℝ} (ht : 2 ≤ t) {n : ℕ}
    (hn : 4 * gaussConst t ^ 2 ≤ t ^ n) : 1 ≤ n := by
  have ht1 : (1 : ℝ) < t := by linarith
  have hGsq : (1 : ℝ) ≤ gaussConst t ^ 2 := one_le_pow₀ (one_le_gaussConst ht1)
  have h4 : (4 : ℝ) ≤ t ^ n := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | h
  · rw [pow_zero] at h4; exact absurd h4 (by norm_num)
  · exact h

/-! ### Dominant-term separation -/

/-- **The head of (23) is at most half the dominant term.**

`|legCoef t n j| ≤ C² t^{degTerm n j} ≤ C² t^{degTerm n n} u^{n-j}` with `u = t^{-n}`
(`degTerm_add_mul_le`), the reversed geometric tail sums to `≤ 2u` (`sum_pow_sub_le`), and
`2 C² u ≤ 1/2` is exactly the hypothesis. -/
theorem abs_head_le {t : ℝ} (ht : 2 ≤ t) {n : ℕ} (hn : 4 * gaussConst t ^ 2 ≤ t ^ n) :
    |∑ j ∈ Finset.range n, legCoef t n j| ≤ t ^ degTerm n n / 2 := by
  have ht1 : (1 : ℝ) < t := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hGsq : (1 : ℝ) ≤ gaussConst t ^ 2 := one_le_pow₀ (one_le_gaussConst ht1)
  have htn : (0 : ℝ) < t ^ n := pow_pos ht0 n
  have hu0 : (0 : ℝ) < (t ^ n)⁻¹ := inv_pos.mpr htn
  -- `gaussConst² · u ≤ 1/4`
  have huq : gaussConst t ^ 2 * (t ^ n)⁻¹ ≤ 1 / 4 := by
    rw [mul_comm, inv_mul_eq_div, div_le_iff₀ htn]
    linarith
  have hu4 : (t ^ n)⁻¹ ≤ 1 / 4 :=
    le_trans (le_mul_of_one_le_left hu0.le hGsq) huq
  -- termwise: `t^{degTerm n j} ≤ t^{degTerm n n} · u^{n-j}`
  have hpow : ∀ j ∈ Finset.range n,
      t ^ degTerm n j ≤ t ^ degTerm n n * ((t ^ n)⁻¹) ^ (n - j) := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hle : degTerm n j + n * (n - j) ≤ degTerm n n := degTerm_add_mul_le (le_of_lt hjn)
    have hkey : t ^ degTerm n j * (t ^ n) ^ (n - j) ≤ t ^ degTerm n n := by
      rw [← pow_mul, ← pow_add]
      exact pow_le_pow_right₀ ht1.le hle
    have hupow : ((t ^ n)⁻¹) ^ (n - j) = ((t ^ n) ^ (n - j))⁻¹ := inv_pow (t ^ n) (n - j)
    rw [hupow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos htn _)]
    exact hkey
  -- assemble
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hb : ∀ j ∈ Finset.range n,
      |legCoef t n j| ≤ gaussConst t ^ 2 * (t ^ degTerm n n * ((t ^ n)⁻¹) ^ (n - j)) := by
    intro j hj
    refine le_trans (abs_legCoef_le_degTerm ht1 (le_of_lt (Finset.mem_range.mp hj))) ?_
    exact mul_le_mul_of_nonneg_left (hpow j hj) (by positivity)
  refine le_trans (Finset.sum_le_sum hb) ?_
  have hfac : ∑ j ∈ Finset.range n, gaussConst t ^ 2 * (t ^ degTerm n n * ((t ^ n)⁻¹) ^ (n - j))
      = gaussConst t ^ 2 * t ^ degTerm n n * ∑ j ∈ Finset.range n, ((t ^ n)⁻¹) ^ (n - j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hfac]
  have hD : (0 : ℝ) < t ^ degTerm n n := pow_pos ht0 _
  have hCD : (0 : ℝ) ≤ gaussConst t ^ 2 * t ^ degTerm n n := by positivity
  have hgeo : ∑ j ∈ Finset.range n, ((t ^ n)⁻¹) ^ (n - j) ≤ 2 * (t ^ n)⁻¹ :=
    sum_pow_sub_le hu0.le (by linarith) n
  calc gaussConst t ^ 2 * t ^ degTerm n n * ∑ j ∈ Finset.range n, ((t ^ n)⁻¹) ^ (n - j)
      ≤ gaussConst t ^ 2 * t ^ degTerm n n * (2 * (t ^ n)⁻¹) :=
        mul_le_mul_of_nonneg_left hgeo hCD
    _ = 2 * (gaussConst t ^ 2 * (t ^ n)⁻¹) * t ^ degTerm n n := by ring
    _ ≤ 2 * (1 / 4) * t ^ degTerm n n :=
        mul_le_mul_of_nonneg_right (by linarith) hD.le
    _ = t ^ degTerm n n / 2 := by ring

/-- **Dominant-term separation, signed.**  `(-1)^n P_n(t^n) ≥ t^{degTerm n n}/2 > 0`.
This is the whole content of the file; `legVal_lower` and `legVal_sign` are corollaries. -/
theorem half_pow_le_signed_legVal {t : ℝ} (ht : 2 ≤ t) {n : ℕ}
    (hn : 4 * gaussConst t ^ 2 ≤ t ^ n) :
    t ^ degTerm n n / 2 ≤ (-1) ^ n * legVal t n := by
  have ht1 : (1 : ℝ) < t := by linarith
  have hsplit : legVal t n = (∑ j ∈ Finset.range n, legCoef t n j) + legCoef t n n := by
    rw [legVal_eq, Finset.sum_range_succ]
  have hexp : ((-1 : ℝ)) ^ n * legVal t n
      = (-1) ^ n * legCoef t n n + (-1) ^ n * ∑ j ∈ Finset.range n, legCoef t n j := by
    rw [hsplit]; ring
  have habs : |(-1 : ℝ) ^ n * ∑ j ∈ Finset.range n, legCoef t n j|
      = |∑ j ∈ Finset.range n, legCoef t n j| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hlow : -(t ^ degTerm n n / 2)
      ≤ (-1 : ℝ) ^ n * ∑ j ∈ Finset.range n, legCoef t n j := by
    have hna := neg_abs_le ((-1 : ℝ) ^ n * ∑ j ∈ Finset.range n, legCoef t n j)
    rw [habs] at hna
    linarith [abs_head_le ht hn]
  have hdiag := pow_degTerm_le_signed_diag ht1 n
  rw [hexp]
  linarith

/-- **The lower bound on `|P_n(t^n)|`.**  `degTerm n n = n(3n−1)/2 = 3n²/2 − n/2`, so this
is `|P_n(t^n)| ≥ t^{3n²/2 − n/2}/2`, matching the measured `log_t |P_n(t^n)| = 145.170` at
`t = 5, n = 10` against `degTerm 10 10 = 145`. -/
theorem legVal_lower {t : ℝ} (ht : 2 ≤ t) {n : ℕ} (hn : 4 * gaussConst t ^ 2 ≤ t ^ n) :
    t ^ degTerm n n / 2 ≤ |legVal t n| := by
  have habs : |(-1 : ℝ) ^ n * legVal t n| = |legVal t n| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  calc t ^ degTerm n n / 2 ≤ (-1 : ℝ) ^ n * legVal t n := half_pow_le_signed_legVal ht hn
    _ ≤ |(-1 : ℝ) ^ n * legVal t n| := le_abs_self _
    _ = |legVal t n| := habs

/-- **The sign, as a by-product.** -/
theorem legVal_sign {t : ℝ} (ht : 2 ≤ t) {n : ℕ} (hn : 4 * gaussConst t ^ 2 ≤ t ^ n) :
    0 < (-1) ^ n * legVal t n := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hpos : (0 : ℝ) < t ^ degTerm n n / 2 := by positivity
  linarith [half_pow_le_signed_legVal ht hn]

theorem legVal_ne_zero {t : ℝ} (ht : 2 ≤ t) {n : ℕ} (hn : 4 * gaussConst t ^ 2 ≤ t ^ n) :
    legVal t n ≠ 0 := by
  intro h
  have := legVal_sign ht hn
  rw [h, mul_zero] at this
  exact lt_irrefl 0 this

/-! ### The sharp remainder bound

`QHarm/Forms.lean`'s `sumsq` gives `P_n(t^n) · R_n = ∑_k q^k P_n(q^k)²/(t^n − q^k)`.  Bound
`(t^n − q^k)⁻¹ ≤ (t^n − 1)⁻¹` termwise, use `QHarm/Orthogonality.lean`'s **exact**
`∑_k q^k P_n(q^k)² = t^{n+1}/(t^{2n+1} − 1)`, then divide by `legVal_lower`.  Nothing here
is lossy except the single factor `2` from `legVal_lower` and the `q^k ≤ 1` in the
denominator. -/

private theorem inv_den_le' {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    ((t : ℝ) ^ n - (t⁻¹) ^ k)⁻¹ ≤ ((t : ℝ) ^ n - 1)⁻¹ := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hti : t⁻¹ < 1 := by
    rw [← one_div, div_lt_one ht0]
    linarith
  have hq : (t⁻¹) ^ k ≤ 1 := pow_le_one₀ (le_of_lt (inv_pos.mpr ht0)) hti.le
  have h1 : (1 : ℝ) < t ^ n := one_lt_pow₀ ht (by omega)
  have hpos : (0 : ℝ) < t ^ n - 1 := by linarith
  have hle : (t : ℝ) ^ n - 1 ≤ t ^ n - (t⁻¹) ^ k := by linarith
  have h := one_div_le_one_div_of_le hpos hle
  rwa [one_div, one_div] at h

/-- The sum-of-squares form, bounded by the exact squared norm. -/
theorem sumsq_le {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) :
    ∑' k : ℕ, (t⁻¹) ^ k * (latVal t n k) ^ 2 / ((t : ℝ) ^ n - (t⁻¹) ^ k)
      ≤ ((t : ℝ) ^ n - 1)⁻¹ * (t ^ (n + 1) / (t ^ (2 * n + 1) - 1)) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hsum1 := summable_sq ht hn
  have hsum2 : Summable (fun k : ℕ =>
      ((t : ℝ) ^ n - 1)⁻¹ * ((t⁻¹) ^ k * (latVal t n k) ^ 2)) :=
    (summable_weight_sq_latVal ht n).mul_left _
  have hle : ∀ k : ℕ,
      (t⁻¹) ^ k * (latVal t n k) ^ 2 / ((t : ℝ) ^ n - (t⁻¹) ^ k)
        ≤ ((t : ℝ) ^ n - 1)⁻¹ * ((t⁻¹) ^ k * (latVal t n k) ^ 2) := by
    intro k
    have hnn : (0 : ℝ) ≤ (t⁻¹) ^ k * (latVal t n k) ^ 2 :=
      mul_nonneg (pow_nonneg (le_of_lt (inv_pos.mpr ht0)) k) (sq_nonneg _)
    rw [div_eq_mul_inv, mul_comm (((t : ℝ) ^ n - 1)⁻¹)]
    exact mul_le_mul_of_nonneg_left (inv_den_le' ht hn k) hnn
  refine le_trans (Summable.tsum_le_tsum hle hsum1 hsum2) (le_of_eq ?_)
  rw [tsum_mul_left]
  congr 1
  simpa only [latVal_def] using norm_sq_value ht n

/-- **The sharp remainder bound.**  Assembled from `sumsq` + `norm_sq_value` + `legVal_lower`.

Compare `QHarm/Forms.lean`'s (private) integer-track bound `|R_n| ≤ t^{-n²}(t^n−1)⁻¹ L_n`:
here the `t^{-n²}` is replaced by `t^{-degTerm n n} = t^{-(3n²−n)/2}`, which is the extra
`t^{n²/2}` of margin the rational track needs. -/
theorem abs_rem_le_sharp {t : ℝ} (ht : 2 ≤ t) {n : ℕ} (hn : 4 * gaussConst t ^ 2 ≤ t ^ n) :
    |rem t n| ≤ (2 * t ^ (n + 1) / ((t ^ n - 1) * (t ^ (2 * n + 1) - 1))) / t ^ degTerm n n := by
  have ht1 : (1 : ℝ) < t := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hn1 : 1 ≤ n := one_le_of_threshold ht hn
  have h1 : (1 : ℝ) < t ^ n := one_lt_pow₀ ht1 (by omega)
  have hden1 : (0 : ℝ) < t ^ n - 1 := by linarith
  have h2 : (1 : ℝ) < t ^ (2 * n + 1) := one_lt_pow₀ ht1 (by omega)
  have hden2 : (0 : ℝ) < t ^ (2 * n + 1) - 1 := by linarith
  have hD : (0 : ℝ) < t ^ degTerm n n := pow_pos ht0 _
  have hD2 : (0 : ℝ) < t ^ degTerm n n / 2 := by positivity
  -- the sum-of-squares form is nonnegative and bounded
  have hSpos := sumsq_pos ht1 hn1
  have hSval := sumsq ht1 hn1
  have hbound := sumsq_le ht1 hn1
  have hrem : t ^ degTerm n n / 2 * |rem t n|
      ≤ ((t : ℝ) ^ n - 1)⁻¹ * (t ^ (n + 1) / (t ^ (2 * n + 1) - 1)) := by
    calc t ^ degTerm n n / 2 * |rem t n| ≤ |legVal t n| * |rem t n| :=
          mul_le_mul_of_nonneg_right (legVal_lower ht hn) (abs_nonneg _)
      _ = |legVal t n * rem t n| := (abs_mul _ _).symm
      _ = ∑' k : ℕ, (t⁻¹) ^ k * (latVal t n k) ^ 2 / ((t : ℝ) ^ n - (t⁻¹) ^ k) := by
          rw [hSval]
          exact abs_of_nonneg hSpos.le
      _ ≤ _ := hbound
  have hfin : |rem t n|
      ≤ (((t : ℝ) ^ n - 1)⁻¹ * (t ^ (n + 1) / (t ^ (2 * n + 1) - 1))) / (t ^ degTerm n n / 2) := by
    rw [le_div_iff₀ hD2]
    calc |rem t n| * (t ^ degTerm n n / 2) = t ^ degTerm n n / 2 * |rem t n| := by ring
      _ ≤ _ := hrem
  refine le_trans hfin (le_of_eq ?_)
  field_simp

/-- The assembly's requested spelling.  `QHarm/Forms.lean` also has an `abs_rem_le`, but
it is `private` there (and is the *lossy* integer-track bound `|R_n| ≤ t^{-n²}(t^n−1)⁻¹L_n`),
so the two names do not collide. -/
theorem abs_rem_le {t : ℝ} (ht : 2 ≤ t) {n : ℕ} (hn : 4 * gaussConst t ^ 2 ≤ t ^ n) :
    |rem t n| ≤ (2 * t ^ (n + 1) / ((t ^ n - 1) * (t ^ (2 * n + 1) - 1))) / t ^ degTerm n n :=
  abs_rem_le_sharp ht hn

/-! ### Eventual forms

The largeness hypothesis `4 gaussConst t ^ 2 ≤ t ^ n` is an eventual condition, because
`gaussConst t` depends on neither `n` nor `j`.  These are the shapes `QHarm/MainRat.lean`
should consume: `∀ᶠ n in atTop` is all the assembly needs. -/

open Filter in
theorem eventually_threshold {t : ℝ} (ht : 2 ≤ t) :
    ∀ᶠ n : ℕ in atTop, 4 * gaussConst t ^ 2 ≤ t ^ n := by
  have ht1 : (1 : ℝ) < t := by linarith
  exact (tendsto_pow_atTop_atTop_of_one_lt ht1).eventually_ge_atTop _

open Filter in
theorem eventually_legVal_lower {t : ℝ} (ht : 2 ≤ t) :
    ∀ᶠ n : ℕ in atTop, t ^ degTerm n n / 2 ≤ |legVal t n| :=
  (eventually_threshold ht).mono fun _ hn => legVal_lower ht hn

open Filter in
theorem eventually_legVal_sign {t : ℝ} (ht : 2 ≤ t) :
    ∀ᶠ n : ℕ in atTop, 0 < (-1) ^ n * legVal t n :=
  (eventually_threshold ht).mono fun _ hn => legVal_sign ht hn

open Filter in
theorem eventually_abs_rem_le {t : ℝ} (ht : 2 ≤ t) :
    ∀ᶠ n : ℕ in atTop,
      |rem t n| ≤ (2 * t ^ (n + 1) / ((t ^ n - 1) * (t ^ (2 * n + 1) - 1))) / t ^ degTerm n n :=
  (eventually_threshold ht).mono fun _ hn => abs_rem_le_sharp ht hn

end QHarm

#print axioms QHarm.degTerm_add_gap
#print axioms QHarm.degTerm_succ_sub
#print axioms QHarm.two_mul_degTerm_diag
#print axioms QHarm.abs_legCoef_le_degTerm
#print axioms QHarm.pow_degTerm_le_signed_diag
#print axioms QHarm.one_le_of_threshold
#print axioms QHarm.abs_head_le
#print axioms QHarm.half_pow_le_signed_legVal
#print axioms QHarm.legVal_lower
#print axioms QHarm.legVal_sign
#print axioms QHarm.legVal_ne_zero
#print axioms QHarm.sumsq_le
#print axioms QHarm.abs_rem_le_sharp
#print axioms QHarm.abs_rem_le
#print axioms QHarm.eventually_threshold
#print axioms QHarm.eventually_legVal_lower
#print axioms QHarm.eventually_legVal_sign
#print axioms QHarm.eventually_abs_rem_le
