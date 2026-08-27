/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QHarm.RatSetup
import QHarm.RatDecomp
import QHarm.QLagrange

/-!
# `QHarm/RatIntegrality.lean` — the two linear forms are integers at a rational base

This is the arithmetic payoff of the rational track.  `QHarm/RatSetup.lean` cleared the two
kinds of denominator separately; `QHarm/RatDecomp.lean` removed every negative power of `t`
from the A-form.  Here the two are composed, and the result is that the single clearing
factor `Q^{C_n} · 𝒟_n` (`C_n = Cexp n = degTerm n n = n(3n−1)/2`, `𝒟_n = Dsharp P Q n`)
makes **both** linear forms integral, term by term, with no extra `P`-power anywhere.

The one genuinely new piece of arithmetic is `gexp_le_Cexp`: the `Q`-exponent produced by
clearing a single summand of the Lagrange short form for `legG t n (t^{-r})` never exceeds
`C_n`.  Doubled and rewritten subtraction-free (`b := n − a`) it is exactly

    0 ≤ (3n − b)(n − b) + (n − b),

so the surplus is `0` precisely at `a = 0`, `r = 0` — the bound is attained, not slack.

## Consumes

* `QHarm/RatSetup.lean` — `Cexp`, `Cexp_eq`, `degTerm_le_Cexp`, `gauss_rat`,
  `QCn_legCoef_mem_Zr`, `QCn_legCombo_mem_Zr`, `QCn_legVal_mem_Zr`,
  `Dsharp_div_mem_Zr`, `Dsharp_mul_mem_Zr`, `one_lt_ratBase`;
* `QHarm/RatDecomp.lean` — `legTail`, `Aform_decomp`;
* `QHarm/LegendreBounds.lean` — `degTerm`, `degTerm_diag`;
* `QHarm/CoefBound.lean` — `two_mul_choose_two_add`;
* `QHarm/QBinom.lean` — `qbin`, `gauss`;
* `QHarm/Cyclotomic.lean` — `Dsharp`;
* `QHarm/Integrality.lean` — the `Zr` subring idiom.

## Main results

* **`gexp_le_Cexp`** — the ℕ inequality
  `a(n−a) + (s−a)n + C(n+1−a, 2) ≤ C_n` for `a ≤ s ≤ n−1`.  Fully proved, axiom-clean.
* **`QCn_legG_mem_Zr`** — `Q^{C_n} · P_n(t^{n−r}) ∈ ℤ` for `r < n`, i.e.
  `Q^{C_n} · legG (P/Q) n ((P/Q)^{−r}) ∈ Zr`.  This is the new content of the file; it is
  what lets block 2 of `Aform_decomp` be cleared without an extra `P`-power.
* **`ratB_mem_Zr` / `ratB_isInt`** — `Q^{C_n} · 𝒟_n · P_n(t^n) ∈ ℤ`.
* **`ratA_mem_Zr` / `ratA_isInt`** — `Q^{C_n} · 𝒟_n · (Q_n(t^n) + P_n(t^n)·head_n) ∈ ℤ`.

Auxiliary but exported: `legGZ` (the explicit integer behind one Lagrange summand) and
`QCn_legG_term` (the per-summand clearing identity).

## What is NOT here

* the Lagrange short form itself — `legG_inv_pow`, which lives in
  `QHarm/QLagrange.lean` and is imported here.
* every size/growth estimate: `𝒟_n^{1/n²} → P^{3/π²}` is `QHarm/Growth.lean`, the remainder
  and `|P_n(t^n)|` bounds are `QHarm/LegendreBounds.lean`;
* the nonvanishing `B_n S − A_n ≠ 0` (sum-of-squares, `QHarm/Forms.lean`);
* the assembly into `master_rat` — `QHarm/MainRat.lean`.
-/

namespace QHarm

open Finset

/-! ## The Lagrange short form

The closed form of `P_n` at the lattice points `t^{n−r}` is `QHarm/QLagrange.lean`'s
`legG_inv_pow`, imported above.  The placeholder that stood here is closed.  The identity was
verified in exact rational arithmetic, and independently re-verified before any Lean was
written (`t ∈ {7/2, 5/2, 11/3, 2, 9/2, 3, 13/4}`, `n = 1..8`, every `r < n`: exact agreement at
every point). -/

/-! ## The ℕ degree count

`Cexp n = degTerm n n = C(n,2) + n²`.  The exponent of `Q` needed to clear the `a`-th summand
of the Lagrange short form is

    g(a) = a·(n − a)          (from `gauss t n a`, via `gauss_rat`)
         + (s − a)·n          (from `gauss t (n+s−a) (s−a)`, via `gauss_rat`)
         + C(n+1−a, 2)        (from `t^{C(n+1−a,2)} = P^{…}/Q^{…}`)

with `s = n − 1 − r`.  The claim is `g(a) ≤ Cexp n` for all `a ≤ s ≤ n − 1`. -/

/-- **The degree count.**  Doubling and substituting `b := n − a`, `c := s − a` reduces this to
`0 ≤ (n − b)·(3n − b + 1)`, which is manifest.  Equality holds exactly at `a = 0`, `s = n − 1`
(i.e. `r = 0`), so the exponent `C_n` is sharp and cannot be lowered. -/
theorem gexp_le_Cexp {n s a : ℕ} (hs : s + 1 ≤ n) (ha : a ≤ s) :
    a * (n - a) + (s - a) * n + (n + 1 - a).choose 2 ≤ Cexp n := by
  obtain ⟨c, rfl⟩ : ∃ c, s = a + c := ⟨s - a, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = a + b := ⟨n - a, by omega⟩
  have hcb : c + 1 ≤ b := by omega
  have e1 : a + b - a = b := by omega
  have e2 : a + c - a = c := by omega
  have e3 : a + b + 1 - a = b + 1 := by omega
  rw [e1, e2, e3, Cexp_eq, degTerm_diag]
  -- `2·C(j,2) + j = j²`, supplied for the two `choose 2` atoms so that `nlinarith`
  -- does not have to treat them as unrelated opaque terms.
  have hX : 2 * (b + 1).choose 2 + (b + 1) = (b + 1) * (b + 1) := two_mul_choose_two_add (b + 1)
  have hY : 2 * (a + b).choose 2 + (a + b) = (a + b) * (a + b) := two_mul_choose_two_add (a + b)
  have hkey : (c + 1) * (a + b) ≤ b * (a + b) := Nat.mul_le_mul hcb le_rfl
  nlinarith [hX, hY, hkey, Nat.zero_le (a * a), Nat.zero_le (a * b), Nat.zero_le a,
    Nat.zero_le b, Nat.zero_le c]

/-! ## Clearing one Lagrange summand -/

/-- The explicit integer behind the `a`-th summand of the Lagrange short form, after
multiplication by `Q^{C_n}`:
`(−1)^a [n,a]_{P,Q} [n+s−a, s−a]_{P,Q} P^{C(n+1−a,2)} Q^{C_n − g(a)}`. -/
def legGZ (P Q : ℤ) (n s a : ℕ) : ℤ :=
  (-1) ^ a * qbin P Q n a * qbin P Q (n + s - a) (s - a) * P ^ ((n + 1 - a).choose 2)
    * Q ^ (Cexp n - (a * (n - a) + (s - a) * n + (n + 1 - a).choose 2))

/-- **The per-summand clearing identity.**  Two applications of `gauss_rat` plus
`(P/Q)^h = P^h/Q^h`; the surviving `Q`-exponent is non-negative by `gexp_le_Cexp`. -/
theorem QCn_legG_term {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) {n s a : ℕ}
    (hs : s + 1 ≤ n) (ha : a ≤ s) :
    (Q : ℝ) ^ Cexp n *
        ((-1 : ℝ) ^ a * gauss ((P : ℝ) / (Q : ℝ)) n a
          * gauss ((P : ℝ) / (Q : ℝ)) (n + s - a) (s - a)
          * (((P : ℝ) / (Q : ℝ)) ^ ((n + 1 - a).choose 2)))
      = (legGZ P Q n s a : ℝ) := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQne : ((Q : ℝ)) ≠ 0 := ne_of_gt hQ0
  have hle := gexp_le_Cexp hs ha
  obtain ⟨e, hgap⟩ :
      ∃ e, (a * (n - a) + (s - a) * n + (n + 1 - a).choose 2) + e = Cexp n :=
    ⟨Cexp n - (a * (n - a) + (s - a) * n + (n + 1 - a).choose 2), by omega⟩
  have hsub : Cexp n - (a * (n - a) + (s - a) * n + (n + 1 - a).choose 2) = e := by omega
  have h1 : (Q : ℝ) ^ (a * (n - a)) * gauss ((P : ℝ) / (Q : ℝ)) n a = (qbin P Q n a : ℝ) :=
    gauss_rat hQ hPQ (by omega)
  have h2 : (Q : ℝ) ^ ((s - a) * n) * gauss ((P : ℝ) / (Q : ℝ)) (n + s - a) (s - a)
      = (qbin P Q (n + s - a) (s - a) : ℝ) := by
    have h := gauss_rat hQ hPQ (show s - a ≤ n + s - a by omega)
    rwa [show n + s - a - (s - a) = n from by omega] at h
  have hP : ((P : ℝ)) ^ ((n + 1 - a).choose 2)
      = (Q : ℝ) ^ ((n + 1 - a).choose 2) * ((((P : ℝ) / (Q : ℝ)) ^ ((n + 1 - a).choose 2))) := by
    rw [div_pow]
    field_simp
  unfold legGZ
  push_cast
  rw [hsub, hP, ← h1, ← h2, ← hgap]
  ring

/-- `(−1)^n ∈ ℤ ⊆ ℝ`. -/
private theorem neg_one_pow_mem_Zr (m : ℕ) : ((-1 : ℝ)) ^ m ∈ Zr := by
  have h : ((((-1 : ℤ) ^ m : ℤ)) : ℝ) = (-1 : ℝ) ^ m := by push_cast; ring
  rw [← h]
  exact intCast_mem_Zr _

/-! ## (I) `Q^{C_n} · P_n(t^{n−r}) ∈ ℤ` -/

/-- **The reflected-point integrality.**  `Q^{C_n} · legG (P/Q) n ((P/Q)^{−r}) ∈ ℤ` for every
`r < n`.  This is what makes block 2 of `Aform_decomp` clear with `𝒟_n` alone.

Verified numerically before formalisation (`t ∈ {7/2, 5/2, 11/3, 9/2, 13/4, 5/3, 8/3}`,
`n = 1..7`, every `r < n`): integral at every point. -/
theorem QCn_legG_mem_Zr {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) {n r : ℕ} (hr : r < n) :
    (Q : ℝ) ^ Cexp n * legG ((P : ℝ) / (Q : ℝ)) n ((((P : ℝ) / (Q : ℝ)) ^ r)⁻¹) ∈ Zr := by
  have ht : (1 : ℝ) < (P : ℝ) / (Q : ℝ) := one_lt_ratBase hQ hPQ
  rw [legG_inv_pow ht hr, mul_left_comm ((Q : ℝ) ^ Cexp n) ((-1 : ℝ) ^ n)]
  refine Subring.mul_mem _ (neg_one_pow_mem_Zr n) ?_
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ fun a ha => ?_
  have ha' : a ≤ n - 1 - r := by
    have := Finset.mem_range.mp ha
    omega
  rw [QCn_legG_term hQ hPQ (show n - 1 - r + 1 ≤ n by omega) ha']
  exact intCast_mem_Zr _

/-! ## (II) The two headline forms

Three purely algebraic regroupings, so that each block of `Aform_decomp` is presented to the
subring closure lemmas in exactly the shape `RatSetup` delivers. -/

private theorem three_block_regroup (q D x y z : ℝ) :
    q * D * (-x + y + z) = -(D * (q * x)) + D * (q * y) + D * (q * z) := by ring

private theorem div_regroup (D q g y : ℝ) : D * (q * (g / y)) = (q * g) * (D * (1 / y)) := by
  ring

private theorem mul_regroup (D q u v : ℝ) : D * (q * (u * v)) = (q * u) * (D * v) := by ring

/-- `Q^{C_n} · 𝒟_n · P_n(t^n) ∈ ℤ`. -/
theorem ratB_mem_Zr {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ) :
    (Q : ℝ) ^ Cexp n * (Dsharp P Q n : ℝ) * legVal ((P : ℝ) / (Q : ℝ)) n ∈ Zr := by
  have hrw : (Q : ℝ) ^ Cexp n * (Dsharp P Q n : ℝ) * legVal ((P : ℝ) / (Q : ℝ)) n
      = (Dsharp P Q n : ℝ) * ((Q : ℝ) ^ Cexp n * legVal ((P : ℝ) / (Q : ℝ)) n) := by ring
  rw [hrw]
  exact Subring.mul_mem _ (intCast_mem_Zr _) (QCn_legVal_mem_Zr hQ hPQ n)

theorem ratB_isInt {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ) :
    ∃ b : ℤ, (Q : ℝ) ^ Cexp n * (Dsharp P Q n : ℝ) * legVal ((P : ℝ) / (Q : ℝ)) n = (b : ℝ) :=
  exists_int_of_mem_Zr (ratB_mem_Zr hQ hPQ n)

/-- Block 1 of `Aform_decomp`: `Q^{C_n} · ∑_{j≤n} j · legCoef` is an integer, by
`QCn_legCombo_mem_Zr` with the integer coefficients `c j = j`. -/
private theorem block_one_mem_Zr {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ) :
    (Q : ℝ) ^ Cexp n *
        (∑ j ∈ Finset.range (n + 1), (j : ℝ) * legCoef ((P : ℝ) / (Q : ℝ)) n j) ∈ Zr := by
  have hrw : (∑ j ∈ Finset.range (n + 1), (j : ℝ) * legCoef ((P : ℝ) / (Q : ℝ)) n j)
      = ∑ j ∈ Finset.range (n + 1),
          ((((j : ℤ)) : ℝ)) * legCoef ((P : ℝ) / (Q : ℝ)) n j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [hrw]
  exact QCn_legCombo_mem_Zr hQ hPQ n (fun j => (j : ℤ)) _
    (fun j hj => Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

/-- The tail sums are integer combinations of the `legCoef`s, so `Q^{C_n} · T_d ∈ ℤ`. -/
private theorem QCn_legTail_mem_Zr {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n d : ℕ) :
    (Q : ℝ) ^ Cexp n * legTail ((P : ℝ) / (Q : ℝ)) n d ∈ Zr := by
  unfold legTail
  have hrw : (∑ j ∈ Finset.Icc d n, legCoef ((P : ℝ) / (Q : ℝ)) n j)
      = ∑ j ∈ Finset.Icc d n, ((((1 : ℤ)) : ℝ)) * legCoef ((P : ℝ) / (Q : ℝ)) n j := by
    simp
  rw [hrw]
  exact QCn_legCombo_mem_Zr hQ hPQ n (fun _ => 1) _ (fun j hj => (Finset.mem_Icc.mp hj).2)

/-- **The A-form is an integer.**  `Q^{C_n} · 𝒟_n · (Q_n(t^n) + P_n(t^n)·head_n) ∈ ℤ`.

The three blocks of `Aform_decomp` clear independently:
`∑_j j·legCoef` by `Q^{C_n}` alone; `P_n(t^{n−r})/(t^r − 1)` by `Q^{C_n}` (result (I)) times
`𝒟_n/(t^r − 1)`; and `T_d · t^d/(t^d − 1)` by `Q^{C_n}·T_d` times `𝒟_n t^d/(t^d − 1)`. -/
theorem ratA_mem_Zr {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ) :
    (Q : ℝ) ^ Cexp n * (Dsharp P Q n : ℝ)
        * (legQval ((P : ℝ) / (Q : ℝ)) n
            + legVal ((P : ℝ) / (Q : ℝ)) n * headSum ((P : ℝ) / (Q : ℝ)) n) ∈ Zr := by
  have ht : (1 : ℝ) < (P : ℝ) / (Q : ℝ) := one_lt_ratBase hQ hPQ
  rw [Aform_decomp ht n, three_block_regroup]
  refine Subring.add_mem _ (Subring.add_mem _ (neg_mem ?_) ?_) ?_
  · -- block 1
    exact Subring.mul_mem _ (intCast_mem_Zr _) (block_one_mem_Zr hQ hPQ n)
  · -- block 2 : the reflected values, cleared by (I) and `𝒟_n/(t^{r+1} − 1)`
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Subring.sum_mem _ fun r hr => ?_
    have hrn : r + 1 < n := by
      have := Finset.mem_range.mp hr
      omega
    rw [div_regroup]
    exact Subring.mul_mem _ (QCn_legG_mem_Zr hQ hPQ hrn)
      (Dsharp_div_mem_Zr hQ hPQ (by omega) (by omega))
  · -- block 3 : the tail sums, cleared by `Q^{C_n}` and `𝒟_n t^{d+1}/(t^{d+1} − 1)`
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Subring.sum_mem _ fun d hd => ?_
    have hdn : d + 1 ≤ n := by
      have := Finset.mem_range.mp hd
      omega
    rw [mul_regroup]
    exact Subring.mul_mem _ (QCn_legTail_mem_Zr hQ hPQ n (d + 1))
      (Dsharp_mul_mem_Zr hQ hPQ (by omega) hdn)

theorem ratA_isInt {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) (n : ℕ) :
    ∃ a : ℤ, (Q : ℝ) ^ Cexp n * (Dsharp P Q n : ℝ)
        * (legQval ((P : ℝ) / (Q : ℝ)) n
            + legVal ((P : ℝ) / (Q : ℝ)) n * headSum ((P : ℝ) / (Q : ℝ)) n) = (a : ℝ) :=
  exists_int_of_mem_Zr (ratA_mem_Zr hQ hPQ n)

end QHarm

#print axioms QHarm.gexp_le_Cexp
#print axioms QHarm.QCn_legG_term
#print axioms QHarm.QCn_legG_mem_Zr
#print axioms QHarm.ratB_mem_Zr
#print axioms QHarm.ratB_isInt
#print axioms QHarm.ratA_mem_Zr
#print axioms QHarm.ratA_isInt
