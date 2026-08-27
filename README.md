# QHarm

A Lean 4 formalization (Mathlib `v4.32.0`, zero `sorry`, axioms exactly
`[propext, Classical.choice, Quot.sound]`) of the irrationality of the `q`-harmonic
(Lambert) series

```
S(t) = ∑_{n ≥ 1} 1/(tⁿ − 1)
```

at rational bases `t = P/Q > 1` whose log-ratio `θ = log Q / log P` satisfies
`θ < 1/2 − 1/π²`, together with the integer-base specialization.

```lean
theorem QHarm.master_rat (t : ℚ) (ht : 1 < t)
    (hθ : Real.log (t.den : ℝ) / Real.log (t.num : ℝ) < 1 / 2 - 1 / Real.pi ^ 2) :
    Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1))

theorem QHarm.master_int (t : ℤ) (ht : 2 ≤ t) :
    Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1))
```

## What is and is not new here

**The mathematics is not new.** The rational-base statement is the irrationality part
of Theorem 2 of P. Bundschuh and K. Väänänen, *Arithmetical investigations of a certain
infinite product*, Compositio Math. **91** (1994), 175–199, at `α = −1`: their condition
`λ = log h(q)/log|q| < (1/2 + 1/π²)⁻¹`, with `λ = 1/(1 − θ)` for `q = P/Q`, is exactly
`θ < 1/2 − 1/π²`, and their theorem is quantitative where this library proves only
irrationality. D. Duverney, J. Théor. Nombres Bordeaux **8** (1996), 173–181, Théorème 2,
gives the same series at rational bases under the narrower window
`θ < (1/3)(1 − 3/π²)`. At `Q = 1` the statement is Erdős's theorem of 1948
(`t = 2`, the Erdős–Borwein constant `1.60669515…`) and P. Borwein's of 1991
(every integer `t ≥ 2`).

**The proof formalized here is not Bundschuh–Väänänen's.** It is the Padé /
orthogonal-polynomial construction of W. Van Assche, *Little q-Legendre polynomials and
irrationality of certain Lambert series*, Ramanujan J. **5** (2001), 295–310
(arXiv:math/0101187), which Van Assche states for integer bases, run at `t = P/Q`. What
had to change for a rational base is the integrality mechanism: Van Assche's rests on the
base being an integer, and it is replaced here by two-variable homogeneous
Gaussian-binomial integrality together with clearing by the homogenized cyclotomic
product `𝒟_n = ∏_{k ≤ n} Φ_k(P, Q)`, whose growth `𝒟_n^{1/n²} → P^{3/π²}` is Mertens'
totient asymptotic. The accompanying `Q`-power exponent `C_n = n(3n−1)/2` is what
produces the threshold `1/2 − 1/π²`.

## Proof architecture

Shared foundation:

* `Basic.lean` — the series `S`, its summability, and the irrationality criterion from a
  sequence of integer linear forms `|Bₙ S − Aₙ| → 0`, `Bₙ S − Aₙ ≠ 0` (Van Assche, Lemma 1).
* `QBinom.lean`, `Legendre.lean`, `LegendreBounds.lean` — Gaussian binomials (the
  two-variable homogeneous `qbin P Q` and the real `gauss`), the little `q`-Legendre
  polynomials `P_n`, `Q_n`, their coefficient bounds, and dominant-term separation in
  Van Assche's equation (23).
* `Orthogonality.lean` — the orthogonality relations, obtained by Lagrange interpolation
  at the nodes `q^j` rather than by a `₃φ₂` summation; only the vanishing half plus the
  exact squared norm are consumed downstream.
* `Pade.lean` — the Padé-type identity relating `P_n`, `Q_n` to the tail of `S`.
* `CoefBound.lean` — the Cauchy–Schwarz step and the coefficient size bounds.

Integer track:

* `Clearing.lean`, `Integrality.lean` — the crude clearing factor
  `clr t n = t^{Mₙ} · Dₙ` with `Dₙ = ∏_{k ≤ n}(t^k − 1)`, and the integrality of the forms.
* `Forms.lean` — the balance sheet `|Bₙ S − Aₙ| = clr · |remₙ| → 0`, with nonvanishing from
  Van Assche's sum-of-squares identity (34).
* `Main.lean` — the assembly of `master_int`.

Rational track:

* `Cyclotomic.lean` — the homogenized cyclotomic polynomials `Φ_k(P, Q)`, the product
  formula `∏_{d ∣ ℓ} Φ_d(P, Q) = P^ℓ − Q^ℓ`, and the sharp clearing `𝒟_n`.
* `Mertens.lean` — `∑_{k ≤ n} φ(k) = 3n²/π² + O(n log n)`, via Möbius inversion and
  `ζ(2)`.
* `Growth.lean` — `𝒟_n^{1/n²} → P^{3/π²}`.
* `RatSetup.lean` — the exponent `C_n`, the two-variable integrality atoms.
* `RatDecomp.lean` — the A-form decomposition. Van Assche's equation (25) is *not* used:
  regrouping the double sum by `d` and applying one partial-fraction identity makes the
  head sum cancel exactly, leaving an expression with no negative powers of `t`.
* `QLagrange.lean` — the closed form for `P_n` at the reflected points `t^{n−r}`, the one
  genuinely new lemma the rational track needs, proved by reflecting the interpolation
  nodes and identifying the resulting divided difference with a complete homogeneous
  symmetric polynomial.
* `RatIntegrality.lean` — integrality of `Q^{C_n} · 𝒟_n · Aₙ` and `· Bₙ`, term by term.
* `RatGrowth.lean` — the rational balance `log|Bₙ S − Aₙ| ≤ log 8 − (3/2)δ(log P)n² + O(n)`
  with `δ = (1/2 − 1/π²) − θ > 0`.
* `MainRat.lean` — the assembly of `master_rat`, including `two_le_of_theta`
  (the threshold already forces `t ≥ 2`, so no case is lost).

* `Reduce.lean` — the three headline statements in the form a Palomar Challenge compares
  them, plus the elementary `Real.log` monotonicity and `π > 3` arithmetic that reduces
  them to the two master theorems. Its `AcceptanceTest` section restates each Challenge
  conclusion verbatim and closes it by a bare term.

## Scope, stated plainly

Proved: `S(P/Q)` is irrational whenever `θ = log Q / log P < 1/2 − 1/π² = 0.3986788…`.
That set is infinite but sparse — for each fixed `Q` it contains only the sufficiently
large `P`. Not proved and not claimed: irrationality at any base with
`θ ≥ 1/2 − 1/π²`, including `t = 3/2` (`θ = 0.6309`), `t = 5/2` (`θ = 0.4307`), `t = 4/3`
and `t = 5/4`; any irrationality measure; any linear-independence or transcendence
statement; and any sharpness or optimality claim for the threshold. Chowla's question,
whether `S(t)` is irrational for *every* rational `t > 1`, is not resolved here.

## Building

```
lake exe cache get && lake build
```

## License

Apache 2.0.
