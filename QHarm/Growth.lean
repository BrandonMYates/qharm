/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QHarm.Cyclotomic
import QHarm.Mertens

/-!
# QHarm/Growth.lean — the growth rate of the sharp clearing factor

`𝒟_n^{1/n²} → P^{3/π²}`, in the logarithmic form the assembly consumes.

## Consumes

* `QHarm/Cyclotomic.lean` — `Dsharp`, `Dsharp_pos`, and above all `log_Dsharp_eq`, the
  `O(n)` Möbius-cancellation estimate
  `|log 𝒟_n − (∑_{k≤n} φ(k))·log P| ≤ n · (P/(P−Q))²`.
* `QHarm/Mertens.lean` — `sum_totient_div_sq_tendsto`, i.e. `(∑_{k≤n} φ(k))/n² → 3/π²`.

Both are finished, `sorry`-free files, so every statement below is proved outright.

## Main results

* `QHarm.log_Dsharp_div_sq_tendsto` — the two-sided limit
  `log 𝒟_n / n² → (3/π²)·log P`. Equivalently `𝒟_n^{1/n²} → P^{3/π²}`; the log form is
  the one the balance is actually written in.
* `QHarm.log_Dsharp_le_eventually` — the one-sided form the balance uses:
  for every `ε > 0`, eventually `log 𝒟_n ≤ ((3/π²)·log P + ε)·n²`.
* `QHarm.Dsharp_rpow_tendsto` — the multiplicative restatement
  `(𝒟_n : ℝ)^(1/n²) → P^(3/π²)`, matching the name of the file. Not consumed downstream,
  but it is the multiplicative shape the growth lemma is usually quoted in, so it is
  recorded here.
* `QHarm.log_Dsharp_div_sq_sub_tendsto_zero` and `QHarm.abs_log_Dsharp_div_sq_le` — the two
  reusable intermediate steps (the `O(n)`-error term dies after division by `n²`, with the
  explicit rate `(P/(P−Q))²/n`).

## The argument, in one line

`log 𝒟_n / n² = ((∑_{k≤n} φ(k)) / n²)·log P + (log 𝒟_n − (∑_{k≤n} φ(k))·log P)/n²`.
Mertens sends the first summand to `(3/π²)·log P`; `log_Dsharp_eq` bounds the numerator of
the second by `n·(P/(P−Q))²`, so the second is `O(1/n) → 0`. That is the whole file: the two
inputs were built to compose, and they do.

**Why `PhiHom_bounds` is not used.** The crude bracket
`(P−Q)^{φ(k)} ≤ Φ_k ≤ (P+Q)^{φ(k)}` gives `log 𝒟_n = (∑φ(k))·log(P±Q) + …`, an error of
order `n²` — the *same* order as the main term, so it cannot see the constant `3/π²` at all.
The cancellation has to come from Möbius inversion, which is exactly what `log_Dsharp_eq`
packages. `PhiHom_bounds` is used in this file only through `Dsharp_pos` (positivity, so
that `Real.log` is applied to a positive real).

## Numerics (checked before any of this was proved)

`𝒟_n` computed exactly in Python from the recursion `Φ_k = (P^k − Q^k)/∏_{d∣k, d<k} Φ_d`
(integral at every step, which independently re-checks `prod_PhiHom`), then
`log 𝒟_n / (n² log P)` against `3/π² = 0.3039636`:

| `n` | `(P,Q) = (2,1)` | `(7,2)` | `(5,3)` |
|---|---|---|---|
| 10 | 0.339788 | 0.322722 | 0.332072 |
| 100 | 0.304521 | 0.304401 | 0.304515 |
| 400 | 0.304255 | 0.304239 | 0.304251 |

Converging to `3/π²`, and — as `log_Dsharp_eq` says it must be — independent of `Q`. The
`O(n)` bound itself was re-measured on the same data: at `(P,Q) = (7,2)`, true error
`0.53 / 1.22 / 2.65 / 0.39` at `n = 10 / 50 / 200 / 400` against the bound
`19.6 / 98 / 392 / 784`. Lossy, and nothing downstream is tight.

## What is NOT here

* The integrality of the rational-base forms — `Q^{C_n}·𝒟_n·A_n, B_n ∈ ℤ`, with
  `C_n = n(3n−1)/2`. That is `QHarm/RatIntegrality.lean`.
* The lower bound `|P_n(t^n)| ≥ t^{(3/2−ε)n²}` on the little q-Legendre value, from
  dominant-term separation in eq. (23). That is `QHarm/LegendreBounds.lean`.
* The final assembly `master_rat` (the balance `θ < 1/2 − 1/π²`). That is
  `QHarm/MainRat.lean` / `QHarm/Reduce.lean`.
* Mertens itself, and the cyclotomic atoms: `QHarm/Mertens.lean`, `QHarm/Cyclotomic.lean`.
* The crude integer-track clearing `∏_{k≤n}(t^k − 1)` — `QHarm/Clearing.lean`. The integer
  track (design decision **D1**) never touches this file.
-/

namespace QHarm

open Finset Filter

/-! ## The error term dies after division by `n²` -/

/-- The `O(n)` Möbius error of `log_Dsharp_eq`, divided by `n²`, is `O(1/n)`.

Explicit rate: for `n ≥ 1` the quantity is at most `(P/(P−Q))²/n`. -/
theorem log_Dsharp_div_sq_sub_tendsto_zero {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) :
    Tendsto (fun n : ℕ =>
        (Real.log ((Dsharp P Q n : ℤ) : ℝ)
          - (∑ k ∈ Finset.Icc 1 n, ((Nat.totient k : ℕ) : ℝ)) * Real.log ((P : ℤ) : ℝ))
        / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_
    (tendsto_const_div_atTop_nhds_zero_nat
      ((((P : ℤ) : ℝ) / (((P : ℤ) : ℝ) - ((Q : ℤ) : ℝ))) ^ 2))
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hn0 2
  have hbound := log_Dsharp_eq hQ hPQ n
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hn2]
  calc |Real.log ((Dsharp P Q n : ℤ) : ℝ)
          - (∑ k ∈ Finset.Icc 1 n, ((Nat.totient k : ℕ) : ℝ)) * Real.log ((P : ℤ) : ℝ)|
        / (n : ℝ) ^ 2
      ≤ ((n : ℝ) * ((((P : ℤ) : ℝ) / (((P : ℤ) : ℝ) - ((Q : ℤ) : ℝ))) ^ 2)) / (n : ℝ) ^ 2 := by
        gcongr
    _ = ((((P : ℤ) : ℝ) / (((P : ℤ) : ℝ) - ((Q : ℤ) : ℝ))) ^ 2) / (n : ℝ) := by
        field_simp

/-! ## The growth limit -/

/-- **Growth of the sharp clearing factor.** `𝒟_n^{1/n²} → P^{3/π²}`, in the log form that
the assembly actually consumes:

    log 𝒟_n / n²  →  (3/π²) · log P.

The `Q`-dependence has vanished entirely, which is the content of the Möbius cancellation:
the atoms `Φ_k(P,Q)` know about `Q`, but their product to `n` does not, to order `n²`. -/
theorem log_Dsharp_div_sq_tendsto {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) :
    Tendsto (fun n : ℕ => Real.log ((Dsharp P Q n : ℤ) : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds ((3 / Real.pi ^ 2) * Real.log ((P : ℤ) : ℝ))) := by
  have hmert : Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.Icc 1 n, ((Nat.totient k : ℕ) : ℝ)) / (n : ℝ) ^ 2
        * Real.log ((P : ℤ) : ℝ))
      atTop (nhds ((3 / Real.pi ^ 2) * Real.log ((P : ℤ) : ℝ))) :=
    sum_totient_div_sq_tendsto.mul_const _
  have hsum := hmert.add (log_Dsharp_div_sq_sub_tendsto_zero hQ hPQ)
  rw [add_zero] at hsum
  refine Tendsto.congr' ?_ hsum
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  field_simp
  ring

/-- The `O(1/n)` rate, spelled out: for `n ≥ 1`,
`|log 𝒟_n / n² − ((∑_{k≤n} φ(k))/n²)·log P| ≤ (P/(P−Q))² / n`.

Not needed for the limit above (which goes through `squeeze_zero_norm'`), but it is the
quantitative statement, and it is what one would use to make the assembly effective. -/
theorem abs_log_Dsharp_div_sq_le {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) {n : ℕ} (hn : 1 ≤ n) :
    |Real.log ((Dsharp P Q n : ℤ) : ℝ) / (n : ℝ) ^ 2
        - (∑ k ∈ Finset.Icc 1 n, ((Nat.totient k : ℕ) : ℝ)) / (n : ℝ) ^ 2
            * Real.log ((P : ℤ) : ℝ)|
      ≤ ((((P : ℤ) : ℝ) / (((P : ℤ) : ℝ) - ((Q : ℤ) : ℝ))) ^ 2) / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hn0 2
  have hbound := log_Dsharp_eq hQ hPQ n
  have hrw : Real.log ((Dsharp P Q n : ℤ) : ℝ) / (n : ℝ) ^ 2
      - (∑ k ∈ Finset.Icc 1 n, ((Nat.totient k : ℕ) : ℝ)) / (n : ℝ) ^ 2
          * Real.log ((P : ℤ) : ℝ)
      = (Real.log ((Dsharp P Q n : ℤ) : ℝ)
          - (∑ k ∈ Finset.Icc 1 n, ((Nat.totient k : ℕ) : ℝ)) * Real.log ((P : ℤ) : ℝ))
        / (n : ℝ) ^ 2 := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hn2]
  calc |Real.log ((Dsharp P Q n : ℤ) : ℝ)
          - (∑ k ∈ Finset.Icc 1 n, ((Nat.totient k : ℕ) : ℝ)) * Real.log ((P : ℤ) : ℝ)|
        / (n : ℝ) ^ 2
      ≤ ((n : ℝ) * ((((P : ℤ) : ℝ) / (((P : ℤ) : ℝ) - ((Q : ℤ) : ℝ))) ^ 2)) / (n : ℝ) ^ 2 := by
        gcongr
    _ = ((((P : ℤ) : ℝ) / (((P : ℤ) : ℝ) - ((Q : ℤ) : ℝ))) ^ 2) / (n : ℝ) := by
        field_simp

/-! ## The one-sided form the balance uses -/

/-- **The eventual upper bound with any margin `ε > 0`.** This is the form the assembly
consumes: the balance only ever needs `𝒟_n` to be *no larger* than `P^{(3/π² + ε)n²}`.

Note there is no `n ≥ N(ε)` bookkeeping to do downstream — `∀ᶠ n in atTop` composes with the
other eventual bounds by `filter_upwards`, and the final contradiction is drawn at a single
large `n`. -/
theorem log_Dsharp_le_eventually {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log ((Dsharp P Q n : ℤ) : ℝ)
        ≤ ((3 / Real.pi ^ 2) * Real.log ((P : ℤ) : ℝ) + ε) * (n : ℝ) ^ 2 := by
  have hlt : ∀ᶠ n : ℕ in atTop,
      Real.log ((Dsharp P Q n : ℤ) : ℝ) / (n : ℝ) ^ 2
        < (3 / Real.pi ^ 2) * Real.log ((P : ℤ) : ℝ) + ε :=
    (log_Dsharp_div_sq_tendsto hQ hPQ).eventually_lt_const (by linarith)
  filter_upwards [hlt, Filter.eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hn0 2
  rw [div_lt_iff₀ hn2] at hn
  linarith

/-! ## The multiplicative restatement -/

/-- **`𝒟_n^{1/n²} → P^{3/π²}`**, literally, as real powers. This is the shape the growth
lemma is usually quoted in; the log form above is the one the Lean assembly uses. Recorded so that
the file's headline claim is present as a theorem and not only as a docstring. -/
theorem Dsharp_rpow_tendsto {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) :
    Tendsto (fun n : ℕ => (((Dsharp P Q n : ℤ) : ℝ)) ^ ((1 : ℝ) / (n : ℝ) ^ 2))
      atTop (nhds (((P : ℤ) : ℝ) ^ (3 / Real.pi ^ 2))) := by
  have hP0 : (0 : ℝ) < ((P : ℤ) : ℝ) := by exact_mod_cast lt_trans hQ hPQ
  have hexp := (Real.continuous_exp.tendsto _).comp (log_Dsharp_div_sq_tendsto hQ hPQ)
  rw [Function.comp_def] at hexp
  have hlim : Real.exp ((3 / Real.pi ^ 2) * Real.log ((P : ℤ) : ℝ))
      = ((P : ℤ) : ℝ) ^ (3 / Real.pi ^ 2) := by
    rw [Real.rpow_def_of_pos hP0, mul_comm]
  rw [hlim] at hexp
  refine Tendsto.congr' ?_ hexp
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hD : (0 : ℝ) < ((Dsharp P Q n : ℤ) : ℝ) := by
    exact_mod_cast Dsharp_pos hQ hPQ n
  rw [Real.rpow_def_of_pos hD]
  ring_nf

/-! ## Interface conformance

The two statements the assembly was specified against, in their literal spelling (`(P : ℝ)`
rather than `((P : ℤ) : ℝ)`, `Filter.atTop` rather than the opened `atTop`). Both close by
`exact`, so the theorems above *are* the requested interface up to notation, not merely
equivalent to it. -/

section Interface

example {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) :
    Filter.Tendsto (fun n : ℕ => Real.log (Dsharp P Q n : ℝ) / (n : ℝ) ^ 2)
      Filter.atTop (nhds ((3 / Real.pi ^ 2) * Real.log (P : ℝ))) :=
  log_Dsharp_div_sq_tendsto hQ hPQ

example {P Q : ℤ} (hQ : 0 < Q) (hPQ : Q < P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.log (Dsharp P Q n : ℝ) ≤ ((3 / Real.pi ^ 2) * Real.log (P : ℝ) + ε) * (n : ℝ) ^ 2 :=
  log_Dsharp_le_eventually hQ hPQ hε

end Interface

/-! ## Axiom audit -/

section AxiomAudit

#print axioms QHarm.log_Dsharp_div_sq_sub_tendsto_zero
#print axioms QHarm.log_Dsharp_div_sq_tendsto
#print axioms QHarm.abs_log_Dsharp_div_sq_le
#print axioms QHarm.log_Dsharp_le_eventually
#print axioms QHarm.Dsharp_rpow_tendsto

end AxiomAudit

end QHarm
