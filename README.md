# QHarm

A Lean 4 formalization (Mathlib `v4.32.0`, zero `sorry`, axioms exactly
`[propext, Classical.choice, Quot.sound]`) of the irrationality of the `q`-harmonic series
at every integer base:

```lean
theorem QHarm.master_int (t : ℤ) (ht : 2 ≤ t) :
    Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1))
```

At `t = 2` this is the irrationality of the Erdős–Borwein constant
`∑ 1/(2ⁿ − 1)` (Erdős, 1948); for general integer `t ≥ 2` it is a theorem of P. Borwein
(1991). The proof formalized here is of the Padé / orthogonal-polynomial type: explicit
linear forms `B_n S − A_n` with integer coefficients that tend to zero without vanishing.

## Proof architecture

* `Basic.lean` — the series `S`, and the irrationality criterion from a sequence of integer
  linear forms `|B_n S − A_n| → 0`, `B_n S − A_n ≠ 0`.
* `QBinom.lean`, `Legendre.lean`, `LegendreBounds.lean` — Gaussian binomials and the little
  `q`-Legendre polynomials, with coefficient and size bounds.
* `Orthogonality.lean` — the orthogonality relations (the vanishing half is what the
  nonvanishing argument needs).
* `Pade.lean` — the Padé-type identity relating the Legendre objects to the tail of `S`.
* `Clearing.lean`, `Integrality.lean`, `CoefBound.lean` — the clearing factor
  `clr t n = t^{M_n} · D_n` that makes the forms integral, and the bounds
  `clr t n ≤ t^{n²}`, `|rem t n| ≤ 2 t^{−n²−n} √(h_n/(1−q))`.
* `Forms.lean` — the balance sheet: `|B_n S − A_n| = clr · |rem| → 0`, with nonvanishing
  from a sum-of-squares identity.
* `Cyclotomic.lean`, `Mertens.lean`, `Growth.lean` — cyclotomic-height and growth
  estimates for the general rational-base track; not needed for `master_int` and included
  as finished, `sorry`-free components.
* `Main.lean` — the assembly of `master_int`, ending with the axiom audit.

The general rational-base theorem that this library was built toward is **not** included
in this repository; it is the subject of separate work.

## Building

```
lake update && lake exe cache get && lake build
```

## License

Apache 2.0.
