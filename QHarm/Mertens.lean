import Mathlib

/-!
# Mertens' totient asymptotic

**Consumes.** Nothing from `QHarm`. `Mathlib` only.

**Main results.**
* `QHarm.sum_totient_asymptotic` — an explicit-constant Mertens bound
  `|∑_{k ≤ n} φ(k) − (3/π²)n²| ≤ 10 · n · log(n+1)` for `n ≥ 1`.
  (`C = 10` is the witness; the proof actually delivers `n(1 + log n) + n/2`.)
* `QHarm.sum_totient_div_sq_tendsto` — the only consequence `QHarm/Growth.lean`
  consumes: `(∑_{k ≤ n} φ(k))/n² → 3/π²`.
* `QHarm.hasSum_moebius_div_sq` — `∑_d μ(d)/d² = 6/π²` (real form).

Reusable intermediate results, all `sorry`-free and exported:
* `QHarm.sum_moebius_mul_id` — `φ = μ * id` pointwise, over `ℝ`.
* `QHarm.sum_Icc_divisorsAntidiagonal` — the Dirichlet interchange
  `∑_{n ≤ N} ∑_{dm = n} F d m = ∑_{d ≤ N} ∑_{m ≤ ⌊N/d⌋} F d m`.
* `QHarm.sum_totient_eq_sum_moebius` — the exact identity
  `∑_{k ≤ N} φ(k) = ∑_{d ≤ N} μ(d)·T(⌊N/d⌋)`, `T m = m(m+1)/2`.
* `QHarm.abs_partial_moebius_sub_le` — the tail bound
  `|∑_{d ≤ N} μ(d)/d² − 6/π²| ≤ 1/N`.
* `QHarm.abs_triangle_sub_le` — `|T(⌊N/d⌋) − N²/(2d²)| ≤ N/d`.
* `QHarm.sum_inv_Icc_le` — `∑_{d ≤ N} 1/d ≤ 1 + log N`.

**What is NOT here.** The cyclotomic clearing factor `D_n = ∏_{k≤n} Φ_k(P,Q)`
(that is `QHarm/Cyclotomic.lean`), the growth statement `D_n^{1/n²} → P^{3/π²}`
(that is `QHarm/Growth.lean`), and anything about the q-series construction.
-/

namespace QHarm

open Finset
open scoped ArithmeticFunction.Moebius

/-! ### Step 1: `φ = μ * id` pointwise -/

/-- Möbius inversion of `∑_{d ∣ n} φ(d) = n`, stated over `ℝ`. -/
theorem sum_moebius_mul_id (n : ℕ) (hn : 0 < n) :
    ∑ p ∈ n.divisorsAntidiagonal, (μ p.1 : ℝ) * (p.2 : ℝ) = (n.totient : ℝ) := by
  refine (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℝ) (f := fun k => (k.totient : ℝ)) (g := fun k => (k : ℝ))).mp ?_ n hn
  intro m _
  exact_mod_cast Nat.sum_totient m

/-! ### Step 2: the Dirichlet interchange -/

/-- The lattice `{(d, m) : 1 ≤ d, 1 ≤ m, d·m ≤ N}` sliced by the product `d·m` versus
sliced by `d`. -/
theorem sum_Icc_divisorsAntidiagonal (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2
      = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), F d m := by
  classical
  have hdisj : (↑(Icc 1 N) : Set ℕ).PairwiseDisjoint
      (fun n => n.divisorsAntidiagonal) := by
    intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    rw [Nat.mem_divisorsAntidiagonal] at hp hp'
    exact hab (hp.1 ▸ hp'.1 ▸ rfl)
  have hbi : (Icc 1 N).biUnion (fun n => n.divisorsAntidiagonal)
      = {p ∈ Icc 1 N ×ˢ Icc 1 N | p.1 * p.2 ≤ N} := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal,
      Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨n, ⟨hn1, hn2⟩, hprod, -⟩
      subst hprod
      have hne : p.1 * p.2 ≠ 0 := by omega
      have h1 : 1 ≤ p.1 := Nat.pos_of_ne_zero fun h => hne (by simp [h])
      have h2 : 1 ≤ p.2 := Nat.pos_of_ne_zero fun h => hne (by simp [h])
      exact ⟨⟨⟨h1, le_trans (Nat.le_mul_of_pos_right _ h2) hn2⟩,
        ⟨h2, le_trans (Nat.le_mul_of_pos_left _ h1) hn2⟩⟩, hn2⟩
    · rintro ⟨⟨⟨h1, -⟩, ⟨h2, -⟩⟩, hle⟩
      have hne : p.1 * p.2 ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
      exact ⟨p.1 * p.2, ⟨by omega, hle⟩, rfl, hne⟩
  rw [← Finset.sum_biUnion hdisj, hbi]
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  have hfil : {m ∈ Icc 1 N | d * m ≤ N} = Icc 1 (N / d) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hm1, -⟩, hle⟩
      exact ⟨hm1, (Nat.le_div_iff_mul_le (by omega)).2 (by rwa [mul_comm])⟩
    · rintro ⟨hm1, hm2⟩
      have hle : d * m ≤ N := by
        rw [mul_comm]; exact (Nat.le_div_iff_mul_le (by omega)).1 hm2
      exact ⟨⟨hm1, le_trans (Nat.le_mul_of_pos_left _ (by omega)) hle⟩, hle⟩
  rw [← hfil, Finset.sum_filter]

/-! ### Step 3: the exact Möbius formula for the summatory totient -/

/-- `T m = m(m+1)/2`. -/
noncomputable def triangle (m : ℕ) : ℝ := (m : ℝ) * ((m : ℝ) + 1) / 2

theorem sum_Icc_cast (M : ℕ) : ∑ m ∈ Icc 1 M, (m : ℝ) = triangle M := by
  induction M with
  | zero => simp [triangle]
  | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, triangle, triangle]
      push_cast
      ring

/-- **The exact identity.** `∑_{k ≤ N} φ(k) = ∑_{d ≤ N} μ(d) · T(⌊N/d⌋)`. -/
theorem sum_totient_eq_sum_moebius (N : ℕ) :
    ∑ k ∈ Icc 1 N, (k.totient : ℝ) = ∑ d ∈ Icc 1 N, (μ d : ℝ) * triangle (N / d) := by
  have h1 : ∑ k ∈ Icc 1 N, (k.totient : ℝ)
      = ∑ k ∈ Icc 1 N, ∑ p ∈ k.divisorsAntidiagonal, (μ p.1 : ℝ) * (p.2 : ℝ) := by
    refine (Finset.sum_congr rfl fun k hk => ?_).symm
    rw [Finset.mem_Icc] at hk
    exact sum_moebius_mul_id k (by omega)
  rw [h1, sum_Icc_divisorsAntidiagonal N (fun a b => (μ a : ℝ) * (b : ℝ))]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.mul_sum, sum_Icc_cast]

/-! ### Step 4: `∑_d μ(d)/d² = 6/π²` -/

theorem summable_moebius_div_sq :
    Summable (fun d : ℕ => (μ d : ℝ) / (d : ℝ) ^ 2) := by
  have hcomp : Summable (fun d : ℕ => 1 / (d : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun d => norm_nonneg _) (fun d => ?_) hcomp)
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
      positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hd2]
    have hnum : |((μ d : ℤ) : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := d)
      exact_mod_cast this
    have h := mul_le_mul_of_nonneg_right hnum (le_of_lt (inv_pos.2 hd2))
    rw [one_mul] at h
    rw [div_eq_mul_inv, one_div]
    exact h

/-- **`∑_{d≥1} μ(d)/d² = 6/π² = 1/ζ(2)`.** Transported from the complex L-series identity
`L ζ s · L μ s = 1` at `s = 2` together with `ζ(2) = π²/6`. -/
theorem hasSum_moebius_div_sq :
    HasSum (fun d : ℕ => (μ d : ℝ) / (d : ℝ) ^ 2) (6 / Real.pi ^ 2) := by
  have hpi : (Real.pi : ℂ) ^ 2 ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hs : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hprod := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (s := (2 : ℂ)) hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, riemannZeta_two] at hprod
  -- so the complex L-series of μ at 2 is 6/π²
  have hLmu : LSeries (fun n : ℕ => ((μ n : ℤ) : ℂ)) 2 = 6 / (Real.pi : ℂ) ^ 2 := by
    field_simp at hprod ⊢
    linear_combination hprod
  -- identify it with the real sum
  have hterm : ∀ n : ℕ, LSeries.term (fun n : ℕ => ((μ n : ℤ) : ℂ)) 2 n
      = (((μ n : ℤ) : ℝ) / (n : ℝ) ^ 2 : ℝ) := by
    intro n
    rw [LSeries.term_of_ne_zero' (by norm_num)]
    push_cast
    congr 1
    rw [show ((2 : ℂ)) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  have hcast : (((∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2 : ℝ)) : ℂ) = 6 / (Real.pi : ℂ) ^ 2 := by
    rw [Complex.ofReal_tsum, ← hLmu, LSeries]
    exact tsum_congr fun n => (hterm n).symm
  have : (∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2) = 6 / Real.pi ^ 2 := by
    have h2 : (((6 : ℝ) / Real.pi ^ 2 : ℝ) : ℂ) = 6 / (Real.pi : ℂ) ^ 2 := by push_cast; ring
    exact_mod_cast hcast.trans h2.symm
  exact this ▸ summable_moebius_div_sq.hasSum

/-! ### Step 5: the tail of the Möbius series -/

private lemma Ioc_zero_eq_Icc_one (k : ℕ) : Finset.Ioc 0 k = Finset.Icc 1 k := by
  ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega

/-- `|∑_{d ≤ N} μ(d)/d² − 6/π²| ≤ 1/N`. -/
theorem abs_partial_moebius_sub_le (N : ℕ) (hN : 1 ≤ N) :
    |(∑ d ∈ Icc 1 N, (μ d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2| ≤ 1 / (N : ℝ) := by
  set f : ℕ → ℝ := fun d => (μ d : ℝ) / (d : ℝ) ^ 2 with hf
  have hf0 : f 0 = 0 := by simp [hf]
  have hset : ∀ M : ℕ, Icc 1 M = (Finset.range (M + 1)).erase 0 := by
    intro M; ext x
    simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
    omega
  have hpart : ∀ M : ℕ, ∑ d ∈ Icc 1 M, f d = ∑ d ∈ Finset.range (M + 1), f d := by
    intro M; rw [hset M, Finset.sum_erase _ hf0]
  have htend : Filter.Tendsto (fun M : ℕ => ∑ d ∈ Icc 1 M, f d) Filter.atTop
      (nhds (6 / Real.pi ^ 2)) := by
    have := hasSum_moebius_div_sq.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    exact this.congr fun M => (hpart M).symm
  have hlim : Filter.Tendsto
      (fun M : ℕ => |(∑ d ∈ Icc 1 M, f d) - ∑ d ∈ Icc 1 N, f d|) Filter.atTop
      (nhds |6 / Real.pi ^ 2 - ∑ d ∈ Icc 1 N, f d|) := (htend.sub_const _).abs
  have hev : ∀ᶠ M : ℕ in Filter.atTop,
      |(∑ d ∈ Icc 1 M, f d) - ∑ d ∈ Icc 1 N, f d| ≤ 1 / (N : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop N] with M hM
    have hsplit : (∑ d ∈ Finset.Ioc 0 N, f d) + ∑ d ∈ Finset.Ioc N M, f d
        = ∑ d ∈ Finset.Ioc 0 M, f d := Finset.sum_Ioc_consecutive f (Nat.zero_le N) hM
    rw [Ioc_zero_eq_Icc_one, Ioc_zero_eq_Icc_one] at hsplit
    have hdiff : (∑ d ∈ Icc 1 M, f d) - ∑ d ∈ Icc 1 N, f d = ∑ d ∈ Finset.Ioc N M, f d := by
      linarith [hsplit]
    rw [hdiff]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ d ∈ Finset.Ioc N M, |f d| ≤ ((d : ℝ) ^ 2)⁻¹ := by
      intro d hd
      rw [Finset.mem_Ioc] at hd
      have hd0 : (0 : ℝ) < (d : ℝ) ^ 2 := by
        have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
        positivity
      have hnum : |((μ d : ℤ) : ℝ)| ≤ 1 := by
        have := ArithmeticFunction.abs_moebius_le_one (n := d)
        exact_mod_cast this
      have h := mul_le_mul_of_nonneg_right hnum (le_of_lt (inv_pos.2 hd0))
      rw [one_mul] at h
      calc |f d| = |((μ d : ℤ) : ℝ)| * ((d : ℝ) ^ 2)⁻¹ := by
            simp only [hf, div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.2 hd0)]
        _ ≤ ((d : ℝ) ^ 2)⁻¹ := h
    refine (Finset.sum_le_sum hb).trans ?_
    have := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := N) (n := M) (by omega) hM
    have hMinv : (0 : ℝ) ≤ (M : ℝ)⁻¹ := by positivity
    rw [one_div]
    linarith
  have := le_of_tendsto hlim hev
  rwa [abs_sub_comm] at this

/-! ### Step 6: the local error `T(⌊N/d⌋) − N²/(2d²)` -/

private lemma tri_abs_aux {x y : ℝ} (hy0 : 0 ≤ y) (h1 : y ≤ x) (h2 : x < y + 1) :
    |y * (y + 1) / 2 - x ^ 2 / 2| ≤ x := by
  have hx0 : 0 ≤ x := le_trans hy0 h1
  have hysq : y ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hy0 h1 2
  have h3 : (x - y) * (x + y) ≤ 1 * (x + y) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- `|T(⌊N/d⌋) − N²/(2d²)| ≤ N/d`. -/
theorem abs_triangle_sub_le (N d : ℕ) (hd : 1 ≤ d) :
    |triangle (N / d) - (N : ℝ) ^ 2 / (2 * (d : ℝ) ^ 2)| ≤ (N : ℝ) / (d : ℝ) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmx : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hd0]
    exact_mod_cast Nat.div_mul_le_self N d
  have hxm : (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hd0]
    have h1 : N < (N / d + 1) * d :=
      (Nat.div_lt_iff_lt_mul (by omega)).1 (Nat.lt_succ_self _)
    exact_mod_cast h1
  have hxx : (N : ℝ) ^ 2 / (2 * (d : ℝ) ^ 2) = ((N : ℝ) / (d : ℝ)) ^ 2 / 2 := by
    field_simp
  rw [hxx, triangle]
  exact tri_abs_aux (Nat.cast_nonneg _) hmx hxm

/-- `∑_{d ≤ N} 1/d ≤ 1 + log N`. -/
theorem sum_inv_Icc_le (N : ℕ) : ∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-! ### Step 7: the theorems -/

/-- **Mertens' totient asymptotic.** Explicit-constant form: `C = 10` works. -/
theorem sum_totient_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |(∑ k ∈ Finset.Icc 1 n, (Nat.totient k : ℝ)) - (3 / Real.pi ^ 2) * (n : ℝ) ^ 2|
        ≤ C * (n : ℝ) * Real.log (n + 1) := by
  refine ⟨10, by norm_num, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have e1 : ∑ d ∈ Icc 1 n, (μ d : ℝ) * (triangle (n / d) - (n : ℝ) ^ 2 / (2 * (d : ℝ) ^ 2))
      = (∑ d ∈ Icc 1 n, (μ d : ℝ) * triangle (n / d))
        - ((n : ℝ) ^ 2 / 2) * ∑ d ∈ Icc 1 n, (μ d : ℝ) / (d : ℝ) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  have hsplit : (∑ k ∈ Finset.Icc 1 n, (Nat.totient k : ℝ)) - (3 / Real.pi ^ 2) * (n : ℝ) ^ 2
      = (∑ d ∈ Icc 1 n, (μ d : ℝ) * (triangle (n / d) - (n : ℝ) ^ 2 / (2 * (d : ℝ) ^ 2)))
        + ((n : ℝ) ^ 2 / 2)
            * ((∑ d ∈ Icc 1 n, (μ d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2) := by
    rw [sum_totient_eq_sum_moebius, e1]; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have hA : |∑ d ∈ Icc 1 n, (μ d : ℝ) * (triangle (n / d) - (n : ℝ) ^ 2 / (2 * (d : ℝ) ^ 2))|
      ≤ (n : ℝ) * (1 + Real.log n) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ d ∈ Icc 1 n,
        |(μ d : ℝ) * (triangle (n / d) - (n : ℝ) ^ 2 / (2 * (d : ℝ) ^ 2))|
          ≤ (n : ℝ) * ((1 : ℝ) / (d : ℝ)) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hnum : |((μ d : ℤ) : ℝ)| ≤ 1 := by
        have := ArithmeticFunction.abs_moebius_le_one (n := d)
        exact_mod_cast this
      rw [abs_mul]
      have hrest := abs_triangle_sub_le n d hd.1
      calc |((μ d : ℤ) : ℝ)| * |triangle (n / d) - (n : ℝ) ^ 2 / (2 * (d : ℝ) ^ 2)|
          ≤ 1 * ((n : ℝ) / (d : ℝ)) :=
            mul_le_mul hnum hrest (abs_nonneg _) zero_le_one
        _ = (n : ℝ) * ((1 : ℝ) / (d : ℝ)) := by ring
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_inv_Icc_le n) (le_of_lt hn0)
  have hB : |((n : ℝ) ^ 2 / 2)
      * ((∑ d ∈ Icc 1 n, (μ d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2)| ≤ (n : ℝ) / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 2)]
    have htail := abs_partial_moebius_sub_le n hn
    calc (n : ℝ) ^ 2 / 2
          * |(∑ d ∈ Icc 1 n, (μ d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2|
        ≤ (n : ℝ) ^ 2 / 2 * (1 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
      _ = (n : ℝ) / 2 := by field_simp
  have hlogn : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hn0 (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hkey : (1 : ℝ) + Real.log (n : ℝ) + 1 / 2 ≤ 10 * Real.log ((n : ℝ) + 1) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hkey (le_of_lt hn0)
  linarith [hA, hB, hmul]

/-- **The consequence `QHarm/Growth.lean` consumes.** -/
theorem sum_totient_div_sq_tendsto :
    Filter.Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (Nat.totient k : ℝ)) / (n : ℝ) ^ 2)
      Filter.atTop (nhds (3 / Real.pi ^ 2)) := by
  obtain ⟨C, hC, hbound⟩ := sum_totient_asymptotic
  rw [← tendsto_sub_nhds_zero_iff]
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
      simpa [Function.comp_def, id] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
    exact h0.comp h1
  have hg : Filter.Tendsto
      (fun n : ℕ => (2 * C) * (Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
    simpa using hlog.const_mul (2 * C)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hnn : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hb := hbound n hn
  have hlpos : (0 : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs]
  have hrw : (∑ k ∈ Finset.Icc 1 n, (Nat.totient k : ℝ)) / (n : ℝ) ^ 2 - 3 / Real.pi ^ 2
      = ((∑ k ∈ Finset.Icc 1 n, (Nat.totient k : ℝ)) - (3 / Real.pi ^ 2) * (n : ℝ) ^ 2)
        / (n : ℝ) ^ 2 := by
    field_simp
  rw [hrw, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 2),
    div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
  refine hb.trans ?_
  have hform : 2 * C * (Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)) * (n : ℝ) ^ 2
      = (2 * C * Real.log ((n : ℝ) + 1) * (n : ℝ) ^ 2) / ((n : ℝ) + 1) := by
    field_simp
  rw [hform, le_div_iff₀ hnn]
  have hprod : 0 ≤ C * (n : ℝ) * Real.log ((n : ℝ) + 1) * ((n : ℝ) - 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC.le hn0.le) hlpos) (by linarith)
  nlinarith [hprod]

#print axioms sum_totient_asymptotic
#print axioms sum_totient_div_sq_tendsto
#print axioms hasSum_moebius_div_sq
#print axioms sum_totient_eq_sum_moebius
#print axioms sum_moebius_mul_id
#print axioms sum_Icc_divisorsAntidiagonal
#print axioms abs_partial_moebius_sub_le
#print axioms abs_triangle_sub_le
#print axioms sum_inv_Icc_le

end QHarm
