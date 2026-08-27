/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QHarm.QBinom
import QHarm.Legendre
import QHarm.LegendreBounds
import QHarm.Cyclotomic
import QHarm.Integrality

/-!
# `QHarm/RatSetup.lean` — the rational base `t = P/Q`: clearing the two kinds of denominator

Everything downstream of the rational track evaluates the little `q`-Legendre machinery at a
**rational** base `t = P/Q` with `0 < Q < P` coprime.  Two entirely different denominators
then appear and this file clears both, once and for all:

* the `Q`-powers hidden inside `gauss t n k` and hence inside `legCoef t n j`, cleared by the
  single exponent `C_n = degTerm n n = n(3n−1)/2` (`Cexp`);
* the atoms `t^ℓ − 1` (`1 ≤ ℓ ≤ n`) coming from the head of the series and from `Q_n`,
  cleared by the sharp cyclotomic factor `𝒟_n = Dsharp P Q n` of `QHarm/Cyclotomic.lean`.

## Consumes

* `QHarm/QBinom.lean` — `qbin` (the two-variable homogeneous Gaussian binomial over `ℤ`),
  `qbin_mul_prod`, `gauss`;
* `QHarm/Legendre.lean` — `legCoef`, `legVal`, `legVal_eq`, `headSum`;
* `QHarm/LegendreBounds.lean` — `degTerm`, `degTerm_add_gap`;
* `QHarm/Cyclotomic.lean` — `Dsharp`, `sub_dvd_Dsharp`;
* `QHarm/Integrality.lean` — the `Zr` subring pattern (`Zr`, `mem_Zr`, `intCast_mem_Zr`,
  `exists_int_of_mem_Zr`), which supplies closure under `Finset.sum` for free.

Every dependency above is `sorry`-free, so every statement below is proved outright.

## Main results

* `one_lt_ratBase`, `ratBase_pow_sub_one_pos` — the two positivity facts every consumer needs.
* `Cexp n = degTerm n n`, and `degTerm_le_Cexp` : `j ≤ n → degTerm n j ≤ Cexp n`.
* **`gauss_rat`** — the two-variable bridge
  `Q^(k(n−k)) · gauss (P/Q) n k = qbin P Q n k`.  This is the `Q ≠ 1` generalisation of
  `QHarm/QBinom.lean`'s `gauss_eq_qbin`, and it is what makes the whole rational track
  term-by-term integral.
* `legCoefZ`, **`legCoef_rat`** — `Q^{C_n} · legCoef (P/Q) n j` is the *explicit* integer
  `(−1)^j P^{C(j,2)} [n,j] [n+j,n] Q^{C_n − degTerm n j}`; the exponent is non-negative
  precisely because `degTerm n j ≤ degTerm n n`.
* `QCn_legCoef_mem_Zr`, `QCn_legCombo_mem_Zr`, `QCn_legVal_isInt` — the membership forms.
  `QCn_legCombo_mem_Zr` is stated for an arbitrary integer-coefficient combination because the
  consumers need three different specialisations of it: `legVal` (`c ≡ 1`), the tail sums
  `∑_{j ≥ d}` and the weighted sum `∑_j j · legCoef t n j`.
* `Dsharp_div_mem_Zr`, `Dsharp_mul_mem_Zr` — `𝒟_n/(t^ℓ − 1)` and `𝒟_n t^ℓ/(t^ℓ − 1)` are
  integers for `1 ≤ ℓ ≤ n`, via `1/(t^ℓ − 1) = Q^ℓ/(P^ℓ − Q^ℓ)` and
  `t^ℓ/(t^ℓ − 1) = P^ℓ/(P^ℓ − Q^ℓ)` together with `sub_dvd_Dsharp`.
* `Dsharp_headSum_mem_Zr` — `𝒟_n · headSum (P/Q) n ∈ ℤ`.  This is the `Q ≠ 1` analogue of
  `QHarm/Integrality.lean`'s `Dr_mul_headSum_mem_Zr`.

## What is NOT here

* the Lagrange short formula for `legG t n ((t^r)⁻¹)` — `QHarm/QLagrange.lean`;
* the A-form / B-form decomposition of the linear forms at rational base, and Van Assche's
  equation (25) — `QHarm/Legendre25.lean`, `QHarm/RatIntegrality.lean`;
* every growth or size bound: `𝒟_n^{1/n²} → P^{3/π²}` is `QHarm/Growth.lean`, and the
  dominant-term separation / remainder estimates are `QHarm/LegendreBounds.lean`;
* the assembly into `master_rat` — `QHarm/MainRat.lean`.
-/

namespace QHarm

open Finset

/-! ### Positivity for a rational base -/

/-- `t = P/Q > 1` whenever `0 < Q < P`. -/
theorem one_lt_ratBase {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) : (1 : ℝ) < (P : ℝ) / (Q : ℝ) := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  rw [lt_div_iff₀ hQ0, one_mul]
  exact_mod_cast hPQ

/-- `t^ℓ − 1 > 0` for `ℓ ≥ 1`. -/
theorem ratBase_pow_sub_one_pos {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (0 : ℝ) < (((P : ℝ) / (Q : ℝ)) ^ ℓ) - 1 := by
  have h := one_lt_pow₀ (one_lt_ratBase hQ hPQ) (by omega : ℓ ≠ 0)
  linarith

/-- `Q^ℓ < P^ℓ` for `ℓ ≥ 1`, derived from `1 < P/Q` so that no `pow_lt_pow_left` naming
question arises. -/
private theorem Qpow_lt_Ppow {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) {s : ℕ} (hs : 1 ≤ s) :
    ((Q : ℝ)) ^ s < ((P : ℝ)) ^ s := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQs : (0 : ℝ) < (Q : ℝ) ^ s := pow_pos hQ0 s
  have h := one_lt_pow₀ (one_lt_ratBase hQ hPQ) (by omega : s ≠ 0)
  rw [div_pow, lt_div_iff₀ hQs, one_mul] at h
  exact h

private theorem sub_pow_pos {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) {s : ℕ} (hs : 1 ≤ s) :
    (0 : ℝ) < (P : ℝ) ^ s - (Q : ℝ) ^ s :=
  sub_pos.mpr (Qpow_lt_Ppow hQ hPQ hs)

/-! ### The clearing exponent -/

/-- The `Q`-clearing exponent `C_n = n(3n−1)/2`, in the subtraction-free spelling
`degTerm n n = C(n,2) + n²` of `QHarm/LegendreBounds.lean`. -/
def Cexp (n : ℕ) : ℕ := degTerm n n

theorem Cexp_eq (n : ℕ) : Cexp n = degTerm n n := rfl

/-- `2·C_n + n = 3n²`, i.e. `C_n = n(3n−1)/2`. -/
theorem two_mul_Cexp (n : ℕ) : 2 * Cexp n + n = 3 * (n * n) := two_mul_degTerm_diag n

theorem degTerm_le_Cexp {n j : ℕ} (h : j ≤ n) : degTerm n j ≤ Cexp n := by
  have hg := degTerm_add_gap h
  unfold Cexp
  omega

/-! ### The two-variable bridge `gauss ↔ qbin` -/

/-- One factor of `gauss` at a rational base: `Q^m · (t^{m+j+1} − 1)/(t^{j+1} − 1)` is the
integer-coefficient ratio `(P^{m+j+1} − Q^{m+j+1})/(P^{j+1} − Q^{j+1})`.  The `Q`-powers
telescope: `Q^{j+1}/Q^{m+j+1} = Q^{-m}`. -/
private theorem factor_rat {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (m j : ℕ) :
    (Q : ℝ) ^ m * ((((P : ℝ) / (Q : ℝ)) ^ (m + j + 1) - 1) /
        ((((P : ℝ) / (Q : ℝ)) ^ (j + 1)) - 1))
      = ((P : ℝ) ^ (m + j + 1) - (Q : ℝ) ^ (m + j + 1)) /
          ((P : ℝ) ^ (j + 1) - (Q : ℝ) ^ (j + 1)) := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQne : ((Q : ℝ)) ≠ 0 := ne_of_gt hQ0
  have hdne : ((P : ℝ) ^ (j + 1) - (Q : ℝ) ^ (j + 1)) ≠ 0 :=
    ne_of_gt (sub_pow_pos hQ hPQ (by omega))
  have hQA : ((Q : ℝ)) ^ (m + j + 1) ≠ 0 := pow_ne_zero _ hQne
  have hQB : ((Q : ℝ)) ^ (j + 1) ≠ 0 := pow_ne_zero _ hQne
  have e1 : (((P : ℝ) / (Q : ℝ)) ^ (m + j + 1) - 1)
      = ((P : ℝ) ^ (m + j + 1) - (Q : ℝ) ^ (m + j + 1)) / ((Q : ℝ) ^ (m + j + 1)) := by
    rw [div_pow]
    field_simp
  have e2 : (((P : ℝ) / (Q : ℝ)) ^ (j + 1) - 1)
      = ((P : ℝ) ^ (j + 1) - (Q : ℝ) ^ (j + 1)) / ((Q : ℝ) ^ (j + 1)) := by
    rw [div_pow]
    field_simp
  have hsplit : ((Q : ℝ)) ^ (m + j + 1) = (Q : ℝ) ^ m * (Q : ℝ) ^ (j + 1) := by
    rw [← pow_add]
    ring_nf
  have hq : ((Q : ℝ)) ^ (m + j + 1) / (Q : ℝ) ^ (j + 1) = (Q : ℝ) ^ m := by
    rw [hsplit, mul_div_assoc, div_self hQB, mul_one]
  rw [e1, e2, div_div_div_comm, hq]
  field_simp

/-- **The two-variable bridge.**  `gauss (P/Q) n k = qbin P Q n k / Q^{k(n−k)}`, stated
multiplicatively so that no division appears. -/
theorem gauss_rat {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) {n k : ℕ} (h : k ≤ n) :
    (Q : ℝ) ^ (k * (n - k)) * gauss ((P : ℝ) / (Q : ℝ)) n k = (qbin P Q n k : ℝ) := by
  have hdne : (∏ j ∈ Finset.range k, ((P : ℝ) ^ (j + 1) - (Q : ℝ) ^ (j + 1))) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun j _ => sub_pow_pos hQ hPQ (by omega)))
  calc (Q : ℝ) ^ (k * (n - k)) * gauss ((P : ℝ) / (Q : ℝ)) n k
      = ∏ j ∈ Finset.range k, ((Q : ℝ) ^ (n - k) *
          ((((P : ℝ) / (Q : ℝ)) ^ (n - k + j + 1) - 1) /
            ((((P : ℝ) / (Q : ℝ)) ^ (j + 1)) - 1))) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul,
          Nat.mul_comm (n - k) k]
        rfl
    _ = ∏ j ∈ Finset.range k, (((P : ℝ) ^ (n - k + j + 1) - (Q : ℝ) ^ (n - k + j + 1)) /
          ((P : ℝ) ^ (j + 1) - (Q : ℝ) ^ (j + 1))) :=
        Finset.prod_congr rfl (fun j _ => factor_rat hQ hPQ (n - k) j)
    _ = (∏ j ∈ Finset.range k, ((P : ℝ) ^ (n - k + j + 1) - (Q : ℝ) ^ (n - k + j + 1))) /
          (∏ j ∈ Finset.range k, ((P : ℝ) ^ (j + 1) - (Q : ℝ) ^ (j + 1))) := by
        rw [Finset.prod_div_distrib]
    _ = (qbin P Q n k : ℝ) := by
        rw [div_eq_iff hdne]
        have h2 := qbin_mul_prod P Q h
        have h3 : ((qbin P Q n k : ℝ)) *
            ∏ j ∈ Finset.range k, ((P : ℝ) ^ (j + 1) - (Q : ℝ) ^ (j + 1))
              = ∏ j ∈ Finset.range k,
                  ((P : ℝ) ^ (n - k + j + 1) - (Q : ℝ) ^ (n - k + j + 1)) := by
          exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h2
        exact h3.symm

/-! ### Clearing `legCoef` -/

/-- The cleared integer behind `legCoef`:
`Q^{C_n} · legCoef (P/Q) n j = (−1)^j P^{C(j,2)} [n,j] [n+j,n] Q^{C_n − degTerm n j}`. -/
def legCoefZ (P Q : ℤ) (n j : ℕ) : ℤ :=
  (-1) ^ j * P ^ (j.choose 2) * qbin P Q n j * qbin P Q (n + j) n * Q ^ (Cexp n - degTerm n j)

theorem legCoef_rat {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) {n j : ℕ} (h : j ≤ n) :
    (Q : ℝ) ^ Cexp n * legCoef ((P : ℝ) / (Q : ℝ)) n j = (legCoefZ P Q n j : ℝ) := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQne : ((Q : ℝ)) ≠ 0 := ne_of_gt hQ0
  obtain ⟨e, hgap⟩ : ∃ e, degTerm n j + e = Cexp n := by
    refine ⟨(n - j) * n + (n - j).choose 2, ?_⟩
    unfold Cexp
    exact degTerm_add_gap h
  have hsub : Cexp n - degTerm n j = e := by omega
  have h1 : (Q : ℝ) ^ (j * (n - j)) * gauss ((P : ℝ) / (Q : ℝ)) n j = (qbin P Q n j : ℝ) :=
    gauss_rat hQ hPQ h
  have h2 : (Q : ℝ) ^ (n * j) * gauss ((P : ℝ) / (Q : ℝ)) (n + j) n
      = (qbin P Q (n + j) n : ℝ) := by
    have := gauss_rat hQ hPQ (Nat.le_add_right n j)
    rwa [show n + j - n = j from by omega] at this
  have hP : ((P : ℝ)) ^ (j.choose 2)
      = (Q : ℝ) ^ (j.choose 2) * (((P : ℝ) / (Q : ℝ)) ^ (j.choose 2)) := by
    rw [div_pow]
    field_simp
  unfold legCoef legCoefZ
  push_cast
  rw [hsub, hP, ← h1, ← h2, ← hgap]
  simp only [degTerm]
  ring

/-- Membership form, for `Subring.sum_mem`. -/
theorem QCn_legCoef_mem_Zr {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) {n j : ℕ} (h : j ≤ n) :
    (Q : ℝ) ^ Cexp n * legCoef ((P : ℝ) / (Q : ℝ)) n j ∈ Zr := by
  rw [legCoef_rat hQ hPQ h]
  exact intCast_mem_Zr _

/-- Any real-linear combination of the `legCoef`s with integer coefficients, scaled by
`Q^{C_n}`, is an integer. -/
theorem QCn_legCombo_mem_Zr {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ)
    (c : ℕ → ℤ) (s : Finset ℕ) (hs : ∀ j ∈ s, j ≤ n) :
    (Q : ℝ) ^ Cexp n * (∑ j ∈ s, (c j : ℝ) * legCoef ((P : ℝ) / (Q : ℝ)) n j) ∈ Zr := by
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ (fun j hj => ?_)
  have hrw : (Q : ℝ) ^ Cexp n * ((c j : ℝ) * legCoef ((P : ℝ) / (Q : ℝ)) n j)
      = (c j : ℝ) * ((Q : ℝ) ^ Cexp n * legCoef ((P : ℝ) / (Q : ℝ)) n j) := by ring
  rw [hrw]
  exact Subring.mul_mem _ (intCast_mem_Zr _) (QCn_legCoef_mem_Zr hQ hPQ (hs j hj))

theorem QCn_legVal_mem_Zr {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ) :
    (Q : ℝ) ^ Cexp n * legVal ((P : ℝ) / (Q : ℝ)) n ∈ Zr := by
  rw [legVal_eq]
  have hrw : ∑ j ∈ Finset.range (n + 1), legCoef ((P : ℝ) / (Q : ℝ)) n j
      = ∑ j ∈ Finset.range (n + 1), (((1 : ℤ) : ℝ)) * legCoef ((P : ℝ) / (Q : ℝ)) n j := by
    simp
  rw [hrw]
  exact QCn_legCombo_mem_Zr hQ hPQ n (fun _ => 1) _
    (fun j hj => Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

theorem QCn_legVal_isInt {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ) :
    ∃ z : ℤ, (Q : ℝ) ^ Cexp n * legVal ((P : ℝ) / (Q : ℝ)) n = (z : ℝ) :=
  exists_int_of_mem_Zr (QCn_legVal_mem_Zr hQ hPQ n)

/-! ### The `Dsharp` clearing of the atoms `t^ℓ − 1`

`1/(t^ℓ − 1) = Q^ℓ/(P^ℓ − Q^ℓ)` and `t^ℓ/(t^ℓ − 1) = P^ℓ/(P^ℓ − Q^ℓ)`, and
`(P^ℓ − Q^ℓ) ∣ Dsharp P Q n` for `1 ≤ ℓ ≤ n` (`Cyclotomic.sub_dvd_Dsharp`). -/

/-- `t^ℓ − 1 = (P^ℓ − Q^ℓ)/Q^ℓ`. -/
private theorem ratBase_pow_sub_one_eq {P Q : ℤ} (hQ : 0 < Q) (ℓ : ℕ) :
    (((P : ℝ) / (Q : ℝ)) ^ ℓ) - 1 = ((P : ℝ) ^ ℓ - (Q : ℝ) ^ ℓ) / ((Q : ℝ) ^ ℓ) := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQne : ((Q : ℝ)) ≠ 0 := ne_of_gt hQ0
  rw [div_pow]
  field_simp

theorem Dsharp_div_mem_Zr {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) {n ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hn : ℓ ≤ n) :
    (Dsharp P Q n : ℝ) * (1 / (((P : ℝ) / (Q : ℝ)) ^ ℓ - 1)) ∈ Zr := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQne : ((Q : ℝ)) ≠ 0 := ne_of_gt hQ0
  have hdne : ((P : ℝ) ^ ℓ - (Q : ℝ) ^ ℓ) ≠ 0 := ne_of_gt (sub_pow_pos hQ hPQ hℓ)
  obtain ⟨c, hc⟩ := sub_dvd_Dsharp (P := P) (Q := Q) hℓ hn
  refine mem_Zr.mpr ⟨c * Q ^ ℓ, ?_⟩
  rw [hc, ratBase_pow_sub_one_eq hQ]
  push_cast
  field_simp

theorem Dsharp_mul_mem_Zr {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) {n ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hn : ℓ ≤ n) :
    (Dsharp P Q n : ℝ) * ((((P : ℝ) / (Q : ℝ)) ^ ℓ) / ((((P : ℝ) / (Q : ℝ)) ^ ℓ) - 1)) ∈ Zr := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQne : ((Q : ℝ)) ≠ 0 := ne_of_gt hQ0
  have hdne : ((P : ℝ) ^ ℓ - (Q : ℝ) ^ ℓ) ≠ 0 := ne_of_gt (sub_pow_pos hQ hPQ hℓ)
  obtain ⟨c, hc⟩ := sub_dvd_Dsharp (P := P) (Q := Q) hℓ hn
  refine mem_Zr.mpr ⟨c * P ^ ℓ, ?_⟩
  rw [hc, ratBase_pow_sub_one_eq hQ, div_pow]
  push_cast
  field_simp

/-- `𝒟_n · headSum` is an integer. -/
theorem Dsharp_headSum_mem_Zr {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ) :
    (Dsharp P Q n : ℝ) * headSum ((P : ℝ) / (Q : ℝ)) n ∈ Zr := by
  unfold headSum
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ (fun k hk => ?_)
  have hk' : k + 1 ≤ n := by
    have := Finset.mem_range.mp hk
    omega
  exact Dsharp_div_mem_Zr hQ hPQ (by omega) hk'

end QHarm

#print axioms QHarm.one_lt_ratBase
#print axioms QHarm.ratBase_pow_sub_one_pos
#print axioms QHarm.degTerm_le_Cexp
#print axioms QHarm.two_mul_Cexp
#print axioms QHarm.gauss_rat
#print axioms QHarm.legCoef_rat
#print axioms QHarm.QCn_legCoef_mem_Zr
#print axioms QHarm.QCn_legCombo_mem_Zr
#print axioms QHarm.QCn_legVal_mem_Zr
#print axioms QHarm.QCn_legVal_isInt
#print axioms QHarm.Dsharp_div_mem_Zr
#print axioms QHarm.Dsharp_mul_mem_Zr
#print axioms QHarm.Dsharp_headSum_mem_Zr
