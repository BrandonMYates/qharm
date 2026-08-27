import Mathlib

/-!
# `QHarm.Basic` — the q-harmonic (Lambert) series and the irrationality criterion

**Consumes.** Nothing from the `QHarm` campaign. Stock Mathlib only. This is the
root of the `QHarm` import DAG.

**Main results.**

* `QHarm.S` — the q-harmonic series `∑_{n ≥ 1} 1/(tⁿ − 1)`, spelled over `ℕ+`
  exactly as in the Challenge statement.
* `QHarm.one_lt_pow_of_one_lt`, `QHarm.pow_sub_one_pos` — the two elementary
  positivity facts every later file needs to divide by `t^k − 1`.
* `QHarm.summable_pnat`, `QHarm.summable_nat` — summability of the series in both
  index spellings, by geometric comparison `1/(t^{k+1} − 1) ≤ (t−1)^{-1} t^{-k}`.
* `QHarm.S_eq_tsum_nat` — the `ℕ+ ↔ ℕ` bridge. Every analysis file downstream works
  over `ℕ`; this is the only place the index shift is done.
* `QHarm.S_sub_head` — head/tail split at `N`.
* `QHarm.S_pos` — positivity of the sum.
* `QHarm.irrational_of_linear_forms` — **Van Assche Lemma 1**, the irrationality
  criterion: if the linear forms `B n · x − A n` are nonzero and arbitrarily small,
  then `x` is irrational. This is the ONE place in the whole development where
  `Irrational` is unfolded.
* `QHarm.irrational_of_linear_forms_tendsto` — the convenience form taking a limit
  plus eventual (here: universal) nonvanishing.

**What is NOT here.** The Padé construction and the explicit linear forms
(`QHarm/Forms.lean`), the Gaussian binomials (`QHarm/QBinom.lean`), the
little-q-Legendre polynomials and their orthogonality (`QHarm/Legendre.lean`,
`QHarm/Orthogonality.lean`), the clearing factors `D_n` (`QHarm/Clearing.lean`,
`QHarm/Cyclotomic.lean`), the degree count (`QHarm/Degree.lean`), the growth
asymptotics (`QHarm/Mertens.lean`, `QHarm/Growth.lean`), and the assembly
(`QHarm/Main.lean`, `QHarm/Reduce.lean`). Nothing in this file knows that `A` and
`B` come from anywhere in particular.
-/

namespace QHarm

/-! ### Elementary positivity -/

private theorem one_le_pow_aux {t : ℝ} (ht : 1 < t) (k : ℕ) : (1 : ℝ) ≤ t ^ k := by
  induction k with
  | zero => simp
  | succ n ih => rw [pow_succ]; nlinarith [ih, ht]

/-- `t > 1` forces `t^(k+1) > 1`. -/
theorem one_lt_pow_of_one_lt {t : ℝ} (ht : 1 < t) (k : ℕ) : 1 < t ^ (k + 1) := by
  rw [pow_succ]
  nlinarith [one_le_pow_aux ht k, ht]

/-- The denominators of the q-harmonic series are positive. -/
theorem pow_sub_one_pos {t : ℝ} (ht : 1 < t) (k : ℕ) : 0 < t ^ (k + 1) - 1 :=
  sub_pos.mpr (one_lt_pow_of_one_lt ht k)

/-! ### The series -/

/-- The q-harmonic (Lambert) series `∑_{n≥1} 1/(tⁿ − 1)`, in the exact `ℕ+` spelling
used by the Challenge statement. -/
noncomputable def S (t : ℝ) : ℝ := ∑' n : ℕ+, 1 / (t ^ (n : ℕ) - 1)

/-! ### Summability

The comparison is `t^{k+1} − 1 ≥ t^{k+1} − t^k = (t−1)·t^k > 0`, hence
`1/(t^{k+1} − 1) ≤ (t−1)^{-1} · (1/t)^k`, and the right-hand side is geometric. -/

private theorem term_le {t : ℝ} (ht : 1 < t) (k : ℕ) :
    1 / (t ^ (k + 1) - 1) ≤ (1 / (t - 1)) * (1 / t) ^ k := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have ht1 : (0 : ℝ) < t - 1 := by linarith
  have hk1 : (1 : ℝ) ≤ t ^ k := one_le_pow_aux ht k
  have hpos : 0 < (t - 1) * t ^ k := mul_pos ht1 (pow_pos ht0 k)
  have hle : (t - 1) * t ^ k ≤ t ^ (k + 1) - 1 := by
    have hid : (t - 1) * t ^ k = t ^ (k + 1) - t ^ k := by ring
    rw [hid]; linarith
  calc 1 / (t ^ (k + 1) - 1) ≤ 1 / ((t - 1) * t ^ k) :=
        one_div_le_one_div_of_le hpos hle
    _ = (1 / (t - 1)) * (1 / t) ^ k := by
        rw [div_pow, one_pow]
        field_simp

theorem summable_nat {t : ℝ} (ht : 1 < t) :
    Summable (fun n : ℕ => 1 / (t ^ (n + 1) - 1)) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hgeo : Summable (fun k : ℕ => (1 / (t - 1)) * (1 / t) ^ k) :=
    Summable.mul_left _
      (summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one ht0]; linarith))
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => term_le ht k) hgeo
  exact le_of_lt (div_pos one_pos (pow_sub_one_pos ht k))

theorem summable_pnat {t : ℝ} (ht : 1 < t) :
    Summable (fun n : ℕ+ => 1 / (t ^ (n : ℕ) - 1)) := by
  rw [← Equiv.summable_iff Equiv.pnatEquivNat.symm]
  exact summable_nat ht

set_option linter.unusedVariables false in
/-- The `ℕ+` sum equals the shifted `ℕ` sum — this is the bridge every later file uses,
because all the analysis is done over `ℕ`.

(The reindexing is in fact unconditional; `ht` is kept in the signature because it is
part of the campaign interface and every call site has it to hand.) -/
theorem S_eq_tsum_nat {t : ℝ} (ht : 1 < t) :
    S t = ∑' n : ℕ, 1 / (t ^ (n + 1) - 1) := by
  rw [S, ← Equiv.tsum_eq Equiv.pnatEquivNat.symm (fun n : ℕ+ => 1 / (t ^ (n : ℕ) - 1))]
  rfl

/-- Head/tail split at `N`. -/
theorem S_sub_head {t : ℝ} (ht : 1 < t) (N : ℕ) :
    S t - ∑ k ∈ Finset.range N, 1 / (t ^ (k + 1) - 1)
      = ∑' n : ℕ, 1 / (t ^ (n + N + 1) - 1) := by
  have h : (∑ k ∈ Finset.range N, 1 / (t ^ (k + 1) - 1))
      + (∑' n : ℕ, 1 / (t ^ (n + N + 1) - 1)) = S t := by
    rw [S_eq_tsum_nat ht]
    exact (summable_nat ht).sum_add_tsum_nat_add N
  linarith

theorem S_pos {t : ℝ} (ht : 1 < t) : 0 < S t := by
  rw [S_eq_tsum_nat ht]
  refine (summable_nat ht).tsum_pos (fun n => ?_) 0 ?_
  · exact le_of_lt (div_pos one_pos (pow_sub_one_pos ht n))
  · exact div_pos one_pos (pow_sub_one_pos ht 0)

/-! ### Van Assche Lemma 1 — the irrationality criterion -/

/-- **Van Assche Lemma 1.** The irrationality criterion. This is the ONE place in the
whole development where `Irrational` is unfolded. -/
theorem irrational_of_linear_forms {x : ℝ} (A B : ℕ → ℤ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
        (B n : ℝ) * x - (A n : ℝ) ≠ 0 ∧ |(B n : ℝ) * x - (A n : ℝ)| < ε) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  have hden : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
  have hd : ((r.den : ℝ)) ≠ 0 := ne_of_gt hden
  obtain ⟨n, hne, hlt⟩ := h (1 / (r.den : ℝ)) (by positivity)
  set m : ℤ := B n * r.num - A n * r.den with hm
  have hr : ((r : ℚ) : ℝ) = (r.num : ℝ) / (r.den : ℝ) := Rat.cast_def r
  have key : ((B n : ℝ) * ((r : ℚ) : ℝ) - (A n : ℝ)) * (r.den : ℝ) = (m : ℝ) := by
    rw [hm, hr]
    push_cast
    field_simp
  have hm0 : m ≠ 0 := by
    intro hz
    apply hne
    have hz' : ((B n : ℝ) * ((r : ℚ) : ℝ) - (A n : ℝ)) * (r.den : ℝ) = 0 := by
      rw [key, hz]; simp
    rcases mul_eq_zero.mp hz' with h' | h'
    · exact h'
    · exact absurd h' hd
  have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hm0
  have h2 : |(B n : ℝ) * ((r : ℚ) : ℝ) - (A n : ℝ)| * (r.den : ℝ) = |(m : ℝ)| := by
    rw [← key, abs_mul, abs_of_pos hden]
  have h3 : |(B n : ℝ) * ((r : ℚ) : ℝ) - (A n : ℝ)| * (r.den : ℝ)
      < (1 / (r.den : ℝ)) * (r.den : ℝ) := mul_lt_mul_of_pos_right hlt hden
  rw [h2, one_div, inv_mul_cancel₀ hd] at h3
  linarith

/-- Convenience form taking a limit plus eventual nonvanishing. -/
theorem irrational_of_linear_forms_tendsto {x : ℝ} (A B : ℕ → ℤ)
    (hne : ∀ n : ℕ, (B n : ℝ) * x - (A n : ℝ) ≠ 0)
    (h0 : Filter.Tendsto (fun n => |(B n : ℝ) * x - (A n : ℝ)|) Filter.atTop (nhds 0)) :
    Irrational x := by
  refine irrational_of_linear_forms A B (fun ε hε => ?_)
  have hev : ∀ᶠ n in Filter.atTop, |(B n : ℝ) * x - (A n : ℝ)| < ε :=
    h0.eventually (gt_mem_nhds hε)
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨n, hne n, hn⟩

end QHarm

#print axioms QHarm.irrational_of_linear_forms
#print axioms QHarm.S_eq_tsum_nat
#print axioms QHarm.summable_pnat
