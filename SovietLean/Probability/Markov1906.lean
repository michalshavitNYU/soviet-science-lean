module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Markov (1906), *Extension of the law of large numbers to quantities depending on each other*

Entry: `entries/probability/1906-markov-law-large-numbers-dependent/`.

A. A. Markov, «Распространение закона больших чисел на величины, зависящие друг от друга»,
Izvestiya Fiz.-Mat. Obshchestva pri Kazanskom Universitete, 2nd series, 15 (1906), no. 4,
135–156. The paper in which Markov chains first appear.

## The paper

**Introduction.** Chebyshev's proof of the law of large numbers works whenever the expectation
of the square of `(x₁ + ⋯ + xₙ) - (a₁ + ⋯ + aₙ)` (`aᵢ` the expectation of `xᵢ`) grows more slowly
than `n²`. Markov shows that this happens in some cases where the `xᵢ` depend on each other.

**§1.** Write `zᵢ = xᵢ - aᵢ`. If the expectation of each product `z_l z_k` (`l ≠ k`) is
negative, then `E (z₁ + ⋯ + zₙ)² < ∑ E z_k²`. Markov gets the sign from an inequality of
Chebyshev for oppositely ordered sequences, and uses the identity
`(z₁ + ⋯ + zₙ)² = ∑ z_k² + 2 z₁ z₂ + 2 (z₁ + z₂) z₃ + ⋯` (p. 138). Example: an urn.

**§2.** The first Markov chain. Trials are linked so that the probability of the event `A` at a
trial is `p'` if `A` occurred at the immediately preceding trial and `p''` otherwise, whatever
the earlier results; with no information, `A` has the same probability `p` at every trial, and
`p = p p' + q p''`. Markov finds the probability `R_m` of `A` at trial `l + m` given `A` at trial
`l`: `R_{m+1} = p'' + (p' - p'') R_m`, `R_m = p + q (p' - p'')^m`. Hence
`E z_l z_k = p q (p' - p'')^{k-l}`, `E (z₁ + ⋯ + zₙ)² < n p q` if `p' < p''` and
`< n p q (1 + p' - p'')/(1 - p' + p'')` if `p' > p''`, and the law of large numbers holds: the
frequency of `A` tends to `p` in probability.

**§3.** A generating function for the number of occurrences of `A` (only its algebra is
formalized here).

**§4.** The Pólya-type urn (each ball drawn is returned with another of the same colour), for
which the law of large numbers fails. Not formalized.

**§5.** The general chain: `x_{k+1}` is independent of `x₁, …, x_{k-1}` once `x_k` is known, with
transition probabilities `p_{α,γ}`, all positive. The conditional expectations
`A^{(i)}_α = ∑_γ p_{α,γ} A^{(i-1)}_γ` contract: the spread `Δ^{(i)}` satisfies
`Δ^{(i)} < H Δ^{(i-1)}` with `0 < H < 1`, so all `A^{(i)}_α` and `a_{k+i}` tend to one limit `a`.
Then `|E z_k (z₁ + ⋯ + z_{k-1})| < D (H + ⋯ + H^{k-1})`, `E (z₁ + ⋯ + zₙ)² < G n`, and the
arithmetic mean tends to `a` in probability: "independence of the quantities is not a necessary
condition for the law of large numbers".

## Formal version

| Paper | Lean | Status |
|---|---|---|
| Introduction: Chebyshev's principle | `chebyshev_principle` | proved |
| p. 138: the identity for `(z₁ + ⋯ + zₙ)²` | `sq_sum_eq`, `integral_dev_sq` | proved |
| p. 138: Chebyshev's inequality for oppositely ordered sequences | `chebyshev_sum_le` | proved |
| §1: negative products ⇒ law of large numbers | `lln_of_cov_nonpos` | proved |
| §5 (end), §2: geometric decay of `E z_l z_k` ⇒ LLN | `lln_of_cov_decay` | proved |
| §2, p. 140: `p = p p' + q p''` | `IsSimpleChain.stationary` | proved |
| §2, p. 141: `R_m = p + q (p' - p'')^m` | `R_eq`, `IsSimpleChain.prob_both` | proved |
| §2, p. 142: `E z_l z_k = p q (p' - p'')^{k-l}` | `IsSimpleChain.cov_eq` | proved |
| §2, p. 142: the bound for `p' ≤ p''` | `IsSimpleChain.second_moment_le_of_nonpos` | proved |
| §2, p. 142: the bound for `p' ≥ p''` | `IsSimpleChain.second_moment_le_of_nonneg` | proved |
| §2: law of large numbers for the simple chain | `IsSimpleChain.lln` | proved |
| §3, p. 144: the recurrence for `Ω_k` | `Omega_recurrence` | proved |
| §3, p. 145: the numerator `A + B t` | `numerator_B` | proved |
| §5, p. 152: `A^{(i)}` lies between the extremes of `A^{(i-1)}` | `T_mem` | proved |
| §5, p. 153: `A^{(i)}_α - A^{(i)}_β ≤ h Δ^{(i-1)}`, `h < 1` | `T_sub_le`, `h_lt_one` | proved |
| §5, p. 154: a constant `H < 1` | `exists_H` | proved |
| §5, p. 154: one limit, `Δ^{(i)} ≤ C H^i` | `iterate_spread`, `iterate_tendsto` | proved |
| §5, p. 155: `|E z_l z_{l+i}| ≤ D H^i` | `IsChain.abs_cov_le` | proved |
| §5: law of large numbers for a chain | `IsChain.lln` | proved |

## How the formal statements match the source

* **Probability.** Markov's "mathematical expectation" is the integral against a probability
  measure `μ`; "with probability arbitrarily close to certainty, the arithmetic mean differs
  arbitrarily little from …" is convergence in probability:
  `μ.real {ω | ε ≤ |(x₀ + ⋯ + x_{n-1})/n - a|} → 0` for every `ε > 0`. Trials and quantities are
  numbered from `0` instead of `1`.
* **Chebyshev's principle** is stated with the hypothesis
  `E((x₀ + ⋯ + x_{n-1}) - (a₀ + ⋯ + a_{n-1}))² / n² → 0`, exactly as in the introduction, and
  proved with Markov's (Chebyshev's) inequality on the square. The variables are assumed square
  integrable (`MemLp _ 2`), which the paper takes for granted.
* **§1.** The paper assumes that increasing any one of the quantities lowers the expectations
  of the others, and deduces `E z_l z_k < 0` from Chebyshev's inequality. We prove that
  inequality in its weighted form (`chebyshev_sum_le`) and, separately, the conclusion
  (`lln_of_cov_nonpos`) from `E z_l z_k ≤ 0`; we do not formalize the passage from the
  monotonicity of conditional expectations to the sign of `E z_l z_k` for general random
  variables. Instead of "`E z_n²` remains finite" we assume a uniform bound, which is what the
  argument uses; and since the paper compares the mean with the mean of the expectations, we
  assume the expectations converge to a limit `a`.
* **§2.** `IsSimpleChain μ X p p₁ p₂` (with `p₁ = p'`, `p₂ = p''`) records the hypotheses: `X k`
  is `1` or `0` as `A` occurs at trial `k` or not; `P(X k = 1) = p` for all `k`; and for every
  event `E` determined by trials `0, …, k`,
  `P(E, X k = 1, X (k+1) = 1) = p' P(E, X k = 1)` and the same with `0` and `p''`. This is
  "probability `p'` if `A` occurred at the immediately preceding trial and `p''` otherwise,
  whatever the results of the other preceding trials". The relation `p = p p' + q p''` is then
  derived, not assumed. The law of large numbers needs `|p' - p''| < 1`, which the paper
  assumes tacitly (it divides by `1 - p' + p''`).
* **§5.** `IsChain μ X P`: `X k` takes values in a finite set `S` of labels (the paper's
  `α, β, γ, …`), `P α γ = p_{α,γ}` does not depend on `k`, and
  `P(E, X k = α, X (k+1) = γ) = p_{α,γ} P(E, X k = α)` for every event `E` determined by
  `X 0, …, X k`. The numerical value of the quantity is `v (X k)`; the paper writes `α` for both
  the label and the value. The paper allows "α, β, γ, …" without saying the list is finite; the
  argument (a constant `H < 1` bounding every `h`) needs finitely many values, and we assume it.
  The initial law `p^{(1)}` is arbitrary. The paper's `A^{(i)}_α` is `(T P)^[i] v α`, its `h` is
  `h P α β`, and its `C` is `M - m` for bounds `m ≤ v ≤ M`.
* **Strict versus non-strict.** The paper's inequalities `<` are proved as `≤`.

## What is not formalized

§4 (the urn for which the law of large numbers fails) and the probabilistic meaning of §3 (that
`Ω_k = ∑_m P_{m,k} ξ^m` with `P_{m,k}` the probability of `m` occurrences in `k` trials) are not
formalized.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace SovietLean.Markov1906

/-! ## The identity on p. 138 -/

/-- p. 138: `(z₁ + ⋯ + zₙ)² = z₁² + ⋯ + zₙ² + 2 z₁ z₂ + 2 (z₁ + z₂) z₃ + ⋯`. -/
theorem sq_sum_eq {R : Type*} [CommRing R] (z : ℕ → R) (n : ℕ) :
    (∑ k ∈ range n, z k) ^ 2 = ∑ k ∈ range n, (z k ^ 2 + 2 * (∑ l ∈ range k, z l) * z k) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, sum_range_succ, ← ih]; ring

/-- `x^k + x^{k-1} + ⋯ + x = x (1 + x + ⋯ + x^{k-1})`. -/
theorem sum_pow_sub {R : Type*} [CommSemiring R] (x : R) (k : ℕ) :
    ∑ l ∈ range k, x ^ (k - l) = x * ∑ j ∈ range k, x ^ j := by
  rw [mul_sum, ← sum_range_reflect]
  refine sum_congr rfl fun j hj ↦ ?_
  have : j < k := mem_range.1 hj
  rw [← pow_succ']; congr 1; omega

/-! ## Chebyshev's principle (introduction) -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The deviation `(x₁ - a₁) + ⋯ + (xₙ - aₙ)` of the sum from the sum of expectations. -/
noncomputable def dev (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range n, (X i ω - ∫ ω', X i ω' ∂μ)

/-- **Chebyshev's principle**, as stated in the introduction: if the mathematical expectation of
the square of `(x₁ + ⋯ + xₙ) - (a₁ + ⋯ + aₙ)` divided by `n²` tends to zero, then for every
`ε > 0` the probability that the arithmetic mean of `x₁, …, xₙ` differs from the arithmetic
mean of `a₁, …, aₙ` by at least `ε` tends to zero. -/
theorem chebyshev_principle (X : ℕ → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (h : Tendsto (fun n : ℕ ↦ (∫ ω, dev (μ := μ) X n ω ^ 2 ∂μ) / (n : ℝ) ^ 2) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | ε ≤ |(∑ i ∈ range n, X i ω) / n
        - (∑ i ∈ range n, ∫ ω', X i ω' ∂μ) / n|}) atTop (𝓝 0) := by
  have hD : ∀ n, MemLp (dev (μ := μ) X n) 2 μ := fun n ↦ by
    have : dev (μ := μ) X n = ∑ i ∈ range n, (X i - fun _ ↦ ∫ ω', X i ω' ∂μ) := by
      funext ω; simp [dev, Finset.sum_apply]
    rw [this]; exact memLp_finsetSum' _ fun i _ ↦ (hX i).sub (memLp_const _)
  have hbound : ∀ n : ℕ, 1 ≤ n → μ.real {ω | ε ≤ |(∑ i ∈ range n, X i ω) / n
        - (∑ i ∈ range n, ∫ ω', X i ω' ∂μ) / n|}
        ≤ (∫ ω, dev (μ := μ) X n ω ^ 2 ∂μ) / (n : ℝ) ^ 2 / ε ^ 2 := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hset : {ω | ε ≤ |(∑ i ∈ range n, X i ω) / n - (∑ i ∈ range n, ∫ ω', X i ω' ∂μ) / n|}
        = {ω | (ε * n) ^ 2 ≤ dev (μ := μ) X n ω ^ 2} := by
      ext ω
      simp only [Set.mem_ofPred_eq, dev, sum_sub_distrib]
      rw [← sub_div, abs_div, abs_of_pos hn', le_div_iff₀ hn', ← sq_abs (_ - _),
        sq_le_sq₀ (by positivity) (abs_nonneg _)]
    rw [hset]
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := μ)
      (Eventually.of_forall fun ω ↦ sq_nonneg (dev (μ := μ) X n ω)) (hD n).integrable_sq
      ((ε * n) ^ 2)
    rw [div_div, le_div_iff₀ (by positivity)]
    calc _ = (ε * n) ^ 2 * μ.real {ω | (ε * n) ^ 2 ≤ dev (μ := μ) X n ω ^ 2} := by ring
      _ ≤ _ := hm
  have hlim : Tendsto (fun n : ℕ ↦ (∫ ω, dev (μ := μ) X n ω ^ 2 ∂μ) / (n : ℝ) ^ 2 / ε ^ 2)
      atTop (𝓝 0) := by simpa using h.div_const (ε ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n ↦ measureReal_nonneg) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn using hbound n hn

/-! ## Second moment of the deviation, term by term -/

/-- Integrating the identity of p. 138:
`E (z₁ + ⋯ + zₙ)² = ∑ₖ (E zₖ² + 2 E (z₁ + ⋯ + z_{k-1}) zₖ)`, with `zᵢ = xᵢ - aᵢ`. -/
theorem integral_dev_sq (X : ℕ → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (n : ℕ) :
    ∫ ω, dev (μ := μ) X n ω ^ 2 ∂μ = ∑ k ∈ range n,
      (∫ ω, (X k ω - ∫ ω', X k ω' ∂μ) ^ 2 ∂μ + 2 * ∑ l ∈ range k,
        ∫ ω, (X l ω - ∫ ω', X l ω' ∂μ) * (X k ω - ∫ ω', X k ω' ∂μ) ∂μ) := by
  set z : ℕ → Ω → ℝ := fun i ω ↦ X i ω - ∫ ω', X i ω' ∂μ with hz
  have hzL : ∀ i, MemLp (z i) 2 μ := fun i ↦ (hX i).sub (memLp_const _)
  have hprod : ∀ l k, Integrable (fun ω ↦ z l ω * z k ω) μ := fun l k ↦
    (hzL l).integrable_mul (hzL k)
  have hsq : ∀ k, Integrable (fun ω ↦ z k ω ^ 2) μ := fun k ↦ (hzL k).integrable_sq
  have : ∀ ω, dev (μ := μ) X n ω ^ 2 = ∑ k ∈ range n,
      (z k ω ^ 2 + 2 * ∑ l ∈ range k, z l ω * z k ω) := by
    intro ω
    rw [dev, sq_sum_eq (fun i ↦ z i ω) n]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [mul_assoc, sum_mul]
  simp_rw [this]
  rw [integral_finsetSum (range n)
    (f := fun k ω ↦ z k ω ^ 2 + 2 * ∑ l ∈ range k, z l ω * z k ω)
    (fun k _ ↦ by exact (hsq k).add ((integrable_finsetSum _ fun l _ ↦ hprod l k).const_mul 2))]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [integral_add (hsq k) ((integrable_finsetSum _ fun l _ ↦ hprod l k).const_mul 2),
    integral_const_mul, integral_finsetSum _ fun l _ ↦ hprod l k]

/-- If `E (z₁ + ⋯ + zₙ)² ≤ G n` and the expectations `aₖ` tend to a limit `a`, then the
arithmetic mean of `x₁, …, xₙ` converges in probability to `a`. -/
theorem lln_of_second_moment_le (X : ℕ → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (G a : ℝ)
    (hG : ∀ n : ℕ, ∫ ω, dev (μ := μ) X n ω ^ 2 ∂μ ≤ G * n)
    (ha : Tendsto (fun k ↦ ∫ ω, X k ω ∂μ) atTop (𝓝 a)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | ε ≤ |(∑ i ∈ range n, X i ω) / n - a|}) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n : ℕ ↦ (∫ ω, dev (μ := μ) X n ω ^ 2 ∂μ) / (n : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have hGn : Tendsto (fun n : ℕ ↦ G / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat G
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hGn
      (Eventually.of_forall fun n ↦ div_nonneg (integral_nonneg fun ω ↦ sq_nonneg _)
        (sq_nonneg _)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_div_iff₀ (by positivity) hn']
    calc _ ≤ G * n * n := mul_le_mul_of_nonneg_right (hG n) hn'.le
      _ = _ := by ring
  have hcheb := chebyshev_principle X hX h2 (half_pos hε)
  have hces := ha.cesaro
  have hclose : ∀ᶠ n : ℕ in atTop,
      |(∑ i ∈ range n, ∫ ω', X i ω' ∂μ) / n - a| < ε / 2 := by
    have := (Metric.tendsto_nhds.1 hces) (ε / 2) (half_pos hε)
    filter_upwards [this] with n hn
    rw [Real.dist_eq] at hn
    simpa [div_eq_inv_mul] using hn
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcheb
    (Eventually.of_forall fun n ↦ measureReal_nonneg) ?_
  filter_upwards [hclose] with n hn
  refine measureReal_mono (fun ω hω ↦ ?_)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have := abs_sub_le ((∑ i ∈ range n, X i ω) / n) ((∑ i ∈ range n, ∫ ω', X i ω' ∂μ) / n) a
  linarith

/-- **§5, final step (and §2).** If the covariances decay geometrically,
`|E zₗ zₖ| ≤ D H^{k-l}` for `l < k` with `0 ≤ H < 1`, the variances are bounded by `D`, and
the expectations `aₖ` tend to `a`, then the arithmetic mean converges in probability to `a`.
The bound `E (z₁ + ⋯ + zₙ)² ≤ G n` is the paper's, with `G = D (1 + 2H/(1-H))`. -/
theorem lln_of_cov_decay (X : ℕ → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) {D H a : ℝ}
    (hH0 : 0 ≤ H) (hH1 : H < 1)
    (hvar : ∀ k, ∫ ω, (X k ω - ∫ ω', X k ω' ∂μ) ^ 2 ∂μ ≤ D)
    (hcov : ∀ l k, l < k →
      |∫ ω, (X l ω - ∫ ω', X l ω' ∂μ) * (X k ω - ∫ ω', X k ω' ∂μ) ∂μ| ≤ D * H ^ (k - l))
    (ha : Tendsto (fun k ↦ ∫ ω, X k ω ∂μ) atTop (𝓝 a)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | ε ≤ |(∑ i ∈ range n, X i ω) / n - a|}) atTop (𝓝 0) := by
  have hD : 0 ≤ D := (integral_nonneg fun ω ↦ sq_nonneg _).trans (hvar 0)
  refine lln_of_second_moment_le X hX (D * (1 + 2 * (H / (1 - H)))) a (fun n ↦ ?_) ha hε
  rw [integral_dev_sq X hX n]
  have hgeom : ∀ k, ∑ l ∈ range k, H ^ (k - l) ≤ H / (1 - H) := by
    intro k
    have : ∑ l ∈ range k, H ^ (k - l) = H * ∑ j ∈ range k, H ^ j := sum_pow_sub H k
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := k) hH0 hH1
    rw [← Finset.range_eq_Ico, pow_zero] at h
    rw [this]
    calc H * ∑ j ∈ range k, H ^ j ≤ H * (1 / (1 - H)) := mul_le_mul_of_nonneg_left h hH0
      _ = H / (1 - H) := by ring
  calc _ ≤ ∑ k ∈ range n, (D + 2 * (D * (H / (1 - H)))) := by
        refine sum_le_sum fun k _ ↦ add_le_add (hvar k) ?_
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        calc _ ≤ ∑ l ∈ range k, D * H ^ (k - l) :=
              sum_le_sum fun l hl ↦ (le_abs_self _).trans (hcov l k (mem_range.1 hl))
          _ = D * ∑ l ∈ range k, H ^ (k - l) := by rw [mul_sum]
          _ ≤ _ := mul_le_mul_of_nonneg_left (hgeom k) hD
    _ = _ := by simp; ring

/-- **§1.** If every product `zₗ zₖ` (`l < k`) has nonpositive expectation and the expectations
of the squares stay bounded, then `E (z₁ + ⋯ + zₙ)² ≤ ∑ E zₖ²`, so the law of large numbers
holds. -/
theorem lln_of_cov_nonpos (X : ℕ → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) {D a : ℝ}
    (hvar : ∀ k, ∫ ω, (X k ω - ∫ ω', X k ω' ∂μ) ^ 2 ∂μ ≤ D)
    (hcov : ∀ l k, l < k →
      ∫ ω, (X l ω - ∫ ω', X l ω' ∂μ) * (X k ω - ∫ ω', X k ω' ∂μ) ∂μ ≤ 0)
    (ha : Tendsto (fun k ↦ ∫ ω, X k ω ∂μ) atTop (𝓝 a)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | ε ≤ |(∑ i ∈ range n, X i ω) / n - a|}) atTop (𝓝 0) := by
  refine lln_of_second_moment_le X hX D a (fun n ↦ ?_) ha hε
  rw [integral_dev_sq X hX n]
  calc _ ≤ ∑ k ∈ range n, D := by
        refine sum_le_sum fun k _ ↦ ?_
        have : ∑ l ∈ range k, ∫ ω, (X l ω - ∫ ω', X l ω' ∂μ) *
            (X k ω - ∫ ω', X k ω' ∂μ) ∂μ ≤ 0 :=
          sum_nonpos fun l hl ↦ hcov l k (mem_range.1 hl)
        linarith [hvar k]
    _ = D * n := by simp [mul_comm]

/-! ## §1: Chebyshev's inequality for oppositely ordered sequences (p. 138) -/

/-- The inequality of Chebyshev used on p. 138: if `z` increases while `a` decreases (on the
support of the weights), then `∑ pᵢ zᵢ aᵢ ≤ (∑ pᵢ zᵢ)(∑ pᵢ aᵢ)` for probability weights `p`.
Markov applies it with `zᵢ` the possible values of `z_l` in increasing order and `aᵢ` the
corresponding conditional expectations of `z_k`; since `∑ pᵢ aᵢ = 0`, the expectation of
`z_l z_k` is negative. -/
theorem chebyshev_sum_le {ι : Type*} (s : Finset ι) (p z a : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hp1 : ∑ i ∈ s, p i = 1)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, (z i - z j) * (a i - a j) ≤ 0) :
    ∑ i ∈ s, p i * z i * a i ≤ (∑ i ∈ s, p i * z i) * (∑ i ∈ s, p i * a i) := by
  have key : ∑ i ∈ s, ∑ j ∈ s, p i * p j * ((z i - z j) * (a i - a j)) ≤ 0 :=
    sum_nonpos fun i hi ↦ sum_nonpos fun j hj ↦
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hp i hi) (hp j hj)) (hanti i hi j hj)
  have expand : ∑ i ∈ s, ∑ j ∈ s, p i * p j * ((z i - z j) * (a i - a j)) =
      2 * ((∑ j ∈ s, p j) * ∑ i ∈ s, p i * z i * a i
        - (∑ i ∈ s, p i * z i) * (∑ i ∈ s, p i * a i)) := by
    have e : ∀ i j, p i * p j * ((z i - z j) * (a i - a j)) =
        p j * (p i * z i * a i) + p i * (p j * z j * a j) - (p i * z i) * (p j * a j)
          - (p i * a i) * (p j * z j) := fun i j ↦ by ring
    simp_rw [e, sum_sub_distrib, sum_add_distrib, ← mul_sum, ← sum_mul]
    simp only [mul_assoc, ← mul_sum]
    ring
  rw [expand, hp1, one_mul] at key
  linarith

/-! ## §2: two trials linked in a chain -/

/-- The σ-algebra of the results of the trials `0, …, k` (the paper numbers them `1, …, k+1`). -/
abbrev past {β : Type*} [MeasurableSpace β] (X : ℕ → Ω → β) (k : ℕ) : MeasurableSpace Ω :=
  ⨆ j ∈ Set.Iic k, MeasurableSpace.comap (X j) inferInstance

theorem measurableSet_past {β : Type*} [MeasurableSpace β] (X : ℕ → Ω → β) {j k : ℕ}
    (hjk : j ≤ k) {s : Set β} (hs : MeasurableSet s) : MeasurableSet[past X k] (X j ⁻¹' s) := by
  have : MeasurableSpace.comap (X j) inferInstance ≤ past X k :=
    le_iSup₂ (f := fun j (_ : j ∈ Set.Iic k) ↦
      MeasurableSpace.comap (X j) (inferInstance : MeasurableSpace β)) j (by simpa using hjk)
  exact this _ ⟨s, hs, rfl⟩

/-- **The hypotheses of §2.** `X k` is `1` if the event `A` occurs at trial `k` and `0`
otherwise. While the results of all trials are unknown, `A` has the same probability `p` at
every trial. Given the results of trials `0, …, k`, the probability of `A` at trial `k + 1` is
`p₁` (the paper's `p'`) if `A` occurred at trial `k` and `p₂` (the paper's `p''`) if not,
"whatever the results of the other preceding trials": the identities hold for every event `E`
determined by trials `0, …, k`. -/
structure IsSimpleChain (μ : Measure Ω) (X : ℕ → Ω → ℝ) (p p₁ p₂ : ℝ) : Prop where
  measurable : ∀ k, Measurable (X k)
  zero_or_one : ∀ k ω, X k ω = 0 ∨ X k ω = 1
  prob : ∀ k, μ.real {ω | X k ω = 1} = p
  after_one : ∀ k (E : Set Ω), MeasurableSet[past X k] E →
    μ.real (E ∩ {ω | X k ω = 1} ∩ {ω | X (k + 1) ω = 1}) = p₁ * μ.real (E ∩ {ω | X k ω = 1})
  after_zero : ∀ k (E : Set Ω), MeasurableSet[past X k] E →
    μ.real (E ∩ {ω | X k ω = 0} ∩ {ω | X (k + 1) ω = 1}) = p₂ * μ.real (E ∩ {ω | X k ω = 0})

/-- The paper's `R_m`: the probability of `A` at trial `l + m` when `A` occurred at trial `l`.
`R₀ = 1`, and `R_{m+1} = R_m p' + (1 - R_m) p'' = p'' + (p' - p'') R_m` (p. 141). -/
def R (p₁ p₂ : ℝ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => p₂ + (p₁ - p₂) * R p₁ p₂ m

theorem R_one (p₁ p₂ : ℝ) : R p₁ p₂ 1 = p₁ := by simp [R]

/-- p. 141: `R_m = p + C (p' - p'')^m` with `C = 1 - p = q`, using `p = p p' + q p''`. -/
theorem R_eq {p p₁ p₂ : ℝ} (hp : p = p * p₁ + (1 - p) * p₂) (m : ℕ) :
    R p₁ p₂ m = p + (1 - p) * (p₁ - p₂) ^ m := by
  induction m with
  | zero => simp [R]
  | succ m ih => rw [R, ih, pow_succ]; linear_combination (-1 : ℝ) * hp

namespace IsSimpleChain

variable {X : ℕ → Ω → ℝ} {p p₁ p₂ : ℝ}

theorem measurableSet_eq (h : IsSimpleChain μ X p p₁ p₂) (k : ℕ) (c : ℝ) :
    MeasurableSet {ω | X k ω = c} :=
  h.measurable k (measurableSet_singleton c)

theorem eq_indicator (h : IsSimpleChain μ X p p₁ p₂) (k : ℕ) :
    X k = Set.indicator {ω | X k ω = 1} 1 := by
  funext ω
  rcases h.zero_or_one k ω with h0 | h1
  · simp [Set.indicator, h0]
  · simp [Set.indicator, h1]

theorem zero_eq_diff (h : IsSimpleChain μ X p p₁ p₂) (E : Set Ω) (k : ℕ) :
    E ∩ {ω | X k ω = 0} = E \ {ω | X k ω = 1} := by
  ext ω
  rcases h.zero_or_one k ω with h0 | h1 <;> simp [*]

theorem zero_eq_compl (h : IsSimpleChain μ X p p₁ p₂) (k : ℕ) :
    {ω | X k ω = 0} = {ω | X k ω = 1}ᶜ := by
  ext ω
  rcases h.zero_or_one k ω with h0 | h1 <;> simp [*]

/-- p. 140: `p = p p' + q p''`. -/
theorem stationary (h : IsSimpleChain μ X p p₁ p₂) : p = p * p₁ + (1 - p) * p₂ := by
  have h1 := h.after_one 0 Set.univ MeasurableSet.univ
  have h0 := h.after_zero 0 Set.univ MeasurableSet.univ
  simp only [Set.univ_inter, zero_add] at h1 h0
  rw [h.zero_eq_compl 0, measureReal_compl (h.measurableSet_eq 0 1), h.prob 0,
    probReal_univ] at h0
  rw [h.prob 0] at h1
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := {ω | X 1 ω = 1})
    (h.measurableSet_eq 0 1)
  rw [h.prob 1, Set.inter_comm, Set.sdiff_eq, Set.inter_comm _ {ω | X 0 ω = 1}ᶜ, h1, h0]
    at hsplit
  linarith

theorem integrable_ind (_h : IsSimpleChain μ X p p₁ p₂) {s : Set Ω} (hs : MeasurableSet s) :
    Integrable (s.indicator (1 : Ω → ℝ)) μ :=
  (integrable_const (1 : ℝ)).indicator hs

theorem memLp (h : IsSimpleChain μ X p p₁ p₂) (k : ℕ) : MemLp (X k) 2 μ := by
  refine MemLp.of_bound (h.measurable k).aestronglyMeasurable 1
    (Eventually.of_forall fun ω ↦ ?_)
  rcases h.zero_or_one k ω with h0 | h1 <;> simp [*]

/-- p. 140: `a_l = p`. -/
theorem integral_eq (h : IsSimpleChain μ X p p₁ p₂) (k : ℕ) : ∫ ω, X k ω ∂μ = p := by
  rw [h.eq_indicator k, integral_indicator_one (h.measurableSet_eq k 1), h.prob k]

/-- p. 141: the probability that `A` occurs at both trials `l` and `l + m` is `p R_m`. -/
theorem prob_both (h : IsSimpleChain μ X p p₁ p₂) (l m : ℕ) :
    μ.real ({ω | X l ω = 1} ∩ {ω | X (l + m) ω = 1}) = p * R p₁ p₂ m := by
  induction m with
  | zero => simp [R, h.prob l]
  | succ m ih =>
    set E := {ω | X l ω = 1}
    set T := {ω | X (l + m) ω = 1}
    set B := {ω | X (l + m + 1) ω = 1}
    have hE : MeasurableSet[past X (l + m)] E :=
      measurableSet_past X (by omega) (measurableSet_singleton 1)
    have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := E ∩ B)
      (h.measurableSet_eq (l + m) 1)
    have e1 : E ∩ B ∩ T = E ∩ T ∩ B := by ext; simp [E, T, B]; tauto
    have e2 : (E ∩ B) \ T = E ∩ {ω | X (l + m) ω = 0} ∩ B := by
      rw [h.zero_eq_diff E (l + m)]; ext; simp [E, T, B]; tauto
    rw [e1, e2, h.after_one (l + m) E hE, h.after_zero (l + m) E hE, ih,
      h.zero_eq_diff E (l + m)] at hsplit
    have hE2 := measureReal_inter_add_sdiff (μ := μ) (s := E) (h.measurableSet_eq (l + m) 1)
    rw [ih, h.prob l] at hE2
    rw [show l + (m + 1) = l + m + 1 by omega, ← hsplit, R]
    have : μ.real (E \ T) = p - p * R p₁ p₂ m := by linarith
    rw [this]; ring

/-- p. 142: `E z_l z_k = p q (p' - p'')^{k - l}`, with `z = x - p`, `q = 1 - p`. -/
theorem cov_eq (h : IsSimpleChain μ X p p₁ p₂) (l m : ℕ) :
    ∫ ω, (X l ω - p) * (X (l + m) ω - p) ∂μ = p * (1 - p) * (p₁ - p₂) ^ m := by
  set A := {ω | X l ω = 1}
  set B := {ω | X (l + m) ω = 1}
  have hA := h.measurableSet_eq l 1
  have hB := h.measurableSet_eq (l + m) 1
  have hfun : (fun ω ↦ (X l ω - p) * (X (l + m) ω - p)) = fun ω ↦
      ((A ∩ B).indicator 1 ω - p * A.indicator 1 ω) - (p * B.indicator 1 ω - p ^ 2) := by
    funext ω
    rcases h.zero_or_one l ω with h0 | h1 <;> rcases h.zero_or_one (l + m) ω with h0' | h1' <;>
      simp [A, B, Set.indicator, *] <;> ring
  rw [hfun, integral_sub, integral_sub, integral_sub, integral_const_mul, integral_const_mul,
    integral_indicator_one (hA.inter hB), integral_indicator_one hA, integral_indicator_one hB,
    prob_both h l m, h.prob l, h.prob (l + m), R_eq h.stationary m]
  · simp; ring
  all_goals first
    | exact (h.integrable_ind (hA.inter hB)).sub ((h.integrable_ind hA).const_mul p)
    | exact ((h.integrable_ind hB).const_mul p).sub (integrable_const _)
    | exact h.integrable_ind (hA.inter hB)
    | exact (h.integrable_ind hA).const_mul p
    | exact (h.integrable_ind hB).const_mul p
    | exact integrable_const _

theorem prob_mem_Icc (h : IsSimpleChain μ X p p₁ p₂) : 0 ≤ p ∧ p ≤ 1 := by
  rw [← h.prob 0]; exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- `E z_l z_k = p q (p' - p'')^{k-l}` for `l ≤ k`, with `z_i = x_i - a_i`. -/
theorem cov_eq' (h : IsSimpleChain μ X p p₁ p₂) {l k : ℕ} (hlk : l ≤ k) :
    ∫ ω, (X l ω - ∫ ω', X l ω' ∂μ) * (X k ω - ∫ ω', X k ω' ∂μ) ∂μ
      = p * (1 - p) * (p₁ - p₂) ^ (k - l) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hlk
  rw [h.integral_eq, h.integral_eq, h.cov_eq l m, Nat.add_sub_cancel_left]

theorem var_eq (h : IsSimpleChain μ X p p₁ p₂) (k : ℕ) :
    ∫ ω, (X k ω - ∫ ω', X k ω' ∂μ) ^ 2 ∂μ = p * (1 - p) := by
  simpa [sq] using h.cov_eq' (le_refl k)

/-- p. 142, the case `p' < p''`: `E (z₁ + ⋯ + zₙ)² ≤ n p q`. -/
theorem second_moment_le_of_nonpos (h : IsSimpleChain μ X p p₁ p₂)
    (hδ1 : -1 < p₁ - p₂) (hδ0 : p₁ - p₂ ≤ 0) (n : ℕ) :
    ∫ ω, dev (μ := μ) X n ω ^ 2 ∂μ ≤ n * (p * (1 - p)) := by
  have hpq : 0 ≤ p * (1 - p) := mul_nonneg h.prob_mem_Icc.1 (by linarith [h.prob_mem_Icc.2])
  rw [integral_dev_sq X h.memLp n]
  calc _ ≤ ∑ k ∈ range n, p * (1 - p) := by
        refine sum_le_sum fun k _ ↦ ?_
        rw [h.var_eq, sum_congr rfl fun l hl ↦ h.cov_eq' (mem_range.1 hl).le, ← mul_sum,
          sum_pow_sub]
        have hg : 0 ≤ ∑ j ∈ range k, (p₁ - p₂) ^ j := by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · simp
          · exact (geom_sum_pos' (by linarith) hk.ne').le
        have : p * (1 - p) * ((p₁ - p₂) * ∑ j ∈ range k, (p₁ - p₂) ^ j) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hpq (mul_nonpos_of_nonpos_of_nonneg hδ0 hg)
        linarith
    _ = _ := by simp

/-- p. 142, the case `p' > p''`: `E (z₁ + ⋯ + zₙ)² ≤ n p q (1 + p' - p'')/(1 - p' + p'')`. -/
theorem second_moment_le_of_nonneg (h : IsSimpleChain μ X p p₁ p₂)
    (hδ0 : 0 ≤ p₁ - p₂) (hδ1 : p₁ - p₂ < 1) (n : ℕ) :
    ∫ ω, dev (μ := μ) X n ω ^ 2 ∂μ ≤
      n * (p * (1 - p) * (1 + p₁ - p₂) / (1 - p₁ + p₂)) := by
  have hpq : 0 ≤ p * (1 - p) := mul_nonneg h.prob_mem_Icc.1 (by linarith [h.prob_mem_Icc.2])
  set δ := p₁ - p₂ with hδ
  have hpos : 0 < 1 - δ := by linarith
  rw [integral_dev_sq X h.memLp n]
  calc _ ≤ ∑ k ∈ range n, p * (1 - p) * (1 + 2 * (δ / (1 - δ))) := by
        refine sum_le_sum fun k _ ↦ ?_
        rw [h.var_eq, sum_congr rfl fun l hl ↦ h.cov_eq' (mem_range.1 hl).le, ← mul_sum,
          sum_pow_sub]
        have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := k) hδ0 hδ1
        rw [← Finset.range_eq_Ico, pow_zero] at hg
        have : δ * ∑ j ∈ range k, δ ^ j ≤ δ / (1 - δ) := by
          calc _ ≤ δ * (1 / (1 - δ)) := mul_le_mul_of_nonneg_left hg hδ0
            _ = _ := by ring
        nlinarith
    _ = _ := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        congr 1
        rw [show 1 + p₁ - p₂ = 1 + δ by ring, show 1 - p₁ + p₂ = 1 - δ by ring]
        field_simp
        ring

/-- **§2, the law of large numbers for the simple chain.** If `|p' - p''| < 1`, then for every
`ε > 0` the probability that the frequency of `A` in the first `n` trials differs from `p` by at
least `ε` tends to zero. -/
theorem lln (h : IsSimpleChain μ X p p₁ p₂) (hδ : |p₁ - p₂| < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | ε ≤ |(∑ i ∈ range n, X i ω) / n - p|}) atTop (𝓝 0) := by
  have hpq : 0 ≤ p * (1 - p) := mul_nonneg h.prob_mem_Icc.1 (by linarith [h.prob_mem_Icc.2])
  refine lln_of_cov_decay X h.memLp (D := p * (1 - p)) (H := |p₁ - p₂|) (abs_nonneg _) hδ
    (fun k ↦ (h.var_eq k).le) (fun l k hlk ↦ ?_) ?_ hε
  · rw [h.cov_eq' hlk.le, abs_mul, abs_of_nonneg hpq, abs_pow]
  · simp_rw [h.integral_eq]; exact tendsto_const_nhds

end IsSimpleChain

/-! ## §3: the generating function (algebraic part) -/

/-- p. 144: from `Φ_k = q' Ψ_{k-1} + q'' Φ_{k-1}` and `Ψ_k = p' ξ Ψ_{k-1} + p'' ξ Φ_{k-1}` (p. 143,
with `q' = 1 - p'`, `q'' = 1 - p''`), the sum `Ω_k = Φ_k + Ψ_k` satisfies
`Ω_{k+1} - (p' ξ + q'') Ω_k + (p' - p'') ξ Ω_{k-1} = 0`. -/
theorem Omega_recurrence {R : Type*} [CommRing R] (p₁ p₂ ξ : R) (Φ Ψ : ℕ → R)
    (hΦ : ∀ k, Φ (k + 1) = (1 - p₁) * Ψ k + (1 - p₂) * Φ k)
    (hΨ : ∀ k, Ψ (k + 1) = p₁ * ξ * Ψ k + p₂ * ξ * Φ k) (k : ℕ) :
    (Φ (k + 2) + Ψ (k + 2)) - (p₁ * ξ + (1 - p₂)) * (Φ (k + 1) + Ψ (k + 1))
      + (p₁ - p₂) * ξ * (Φ k + Ψ k) = 0 := by
  rw [hΦ (k + 1), hΨ (k + 1), hΦ k, hΨ k]; ring

/-- p. 144–145: with `Ω₀ = 1` and `Ω₁ = q + p ξ`, the numerator `A + B t` of the generating
function has `A = 1` and `B = Ω₁ - (p' ξ + q'') = (p'' - p')(q ξ + p)`, using
`p = p p' + q p''`. -/
theorem numerator_B {p p₁ p₂ ξ : ℝ} (hp : p = p * p₁ + (1 - p) * p₂) :
    ((1 - p) + p * ξ) - (p₁ * ξ + (1 - p₂)) = (p₂ - p₁) * ((1 - p) * ξ + p) := by
  linear_combination (ξ - 1) * hp

/-! ## §5: quantities linked in a chain, general finite case

The possible values of the quantities are labelled by a finite type `S` (the paper's
`α, β, γ, …`), and `P α γ` is the paper's `p_{α,γ}`. The operator `T f α = ∑_γ p_{α,γ} f γ` takes
the conditional expectations one step back: `A^{(i)}_α = (T^i v) α` (p. 152), where `v α` is the
numerical value labelled `α`. -/

section Contraction

variable {S : Type*} [Fintype S]

/-- `(T f) α = ∑_γ p_{α,γ} f γ`. -/
def T (P : S → S → ℝ) (f : S → ℝ) (α : S) : ℝ := ∑ γ, P α γ * f γ

/-- The paper's `h` for the pair `α, β` (p. 153): the sum of the positive numbers among
`p_{α,γ} - p_{β,γ}`. -/
def h (P : S → S → ℝ) (α β : S) : ℝ := ∑ γ, max (P α γ - P β γ) 0

variable {P : S → S → ℝ}

/-- p. 152: each `A^{(i)}` lies between the greatest and the least of the `A^{(i-1)}`. -/
theorem T_mem (hP : ∀ α γ, 0 ≤ P α γ) (hP1 : ∀ α, ∑ γ, P α γ = 1) {f : S → ℝ} {m M : ℝ}
    (hf : ∀ γ, m ≤ f γ ∧ f γ ≤ M) (α : S) : m ≤ T P f α ∧ T P f α ≤ M := by
  constructor
  · calc m = ∑ γ, P α γ * m := by rw [← sum_mul, hP1, one_mul]
      _ ≤ _ := sum_le_sum fun γ _ ↦ mul_le_mul_of_nonneg_left (hf γ).1 (hP α γ)
  · calc T P f α ≤ ∑ γ, P α γ * M :=
          sum_le_sum fun γ _ ↦ mul_le_mul_of_nonneg_left (hf γ).2 (hP α γ)
      _ = M := by rw [← sum_mul, hP1, one_mul]

/-- p. 153: `A^{(i)}_α - A^{(i)}_β ≤ h Δ^{(i-1)}`, where `Δ^{(i-1)}` bounds the spread of the
`A^{(i-1)}`. -/
theorem T_sub_le (hP1 : ∀ α, ∑ γ, P α γ = 1) {f : S → ℝ} {m M : ℝ}
    (hf : ∀ γ, m ≤ f γ ∧ f γ ≤ M) (α β : S) :
    T P f α - T P f β ≤ h P α β * (M - m) := by
  have hsum : ∑ γ, (P α γ - P β γ) * m = 0 := by
    rw [← sum_mul, sum_sub_distrib, hP1, hP1, sub_self, zero_mul]
  calc T P f α - T P f β = ∑ γ, (P α γ - P β γ) * (f γ - m) := by
        simp only [T, mul_sub, sub_mul, sum_sub_distrib] at hsum ⊢; linarith
    _ ≤ ∑ γ, max (P α γ - P β γ) 0 * (M - m) := by
        refine sum_le_sum fun γ _ ↦ ?_
        have h0 : 0 ≤ f γ - m := by linarith [(hf γ).1]
        calc (P α γ - P β γ) * (f γ - m) ≤ max (P α γ - P β γ) 0 * (f γ - m) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) h0
          _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [(hf γ).2]) (le_max_right _ _)
    _ = _ := by rw [h, sum_mul]

/-- p. 153: if all `p_{α,γ}` are positive, each `h` is less than one. -/
theorem h_lt_one (hP : ∀ α γ, 0 < P α γ) (hP1 : ∀ α, ∑ γ, P α γ = 1) (α β : S) :
    h P α β < 1 := by
  rw [← hP1 α]
  have : Nonempty S := ⟨α⟩
  refine sum_lt_sum_of_nonempty univ_nonempty fun γ _ ↦ max_lt ?_ (hP α γ)
  linarith [hP β γ]

theorem h_nonneg (α β : S) : 0 ≤ h P α β := sum_nonneg fun _ _ ↦ le_max_right _ _

/-- p. 154: a constant `H < 1` bounding every `h`. -/
theorem exists_H (hP : ∀ α γ, 0 < P α γ) (hP1 : ∀ α, ∑ γ, P α γ = 1) :
    ∃ H, 0 ≤ H ∧ H < 1 ∧ ∀ α β, h P α β ≤ H := by
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨0, le_rfl, one_pos, fun α ↦ hS.elim α⟩
  · refine ⟨univ.sup' univ_nonempty fun ab : S × S ↦ h P ab.1 ab.2, ?_, ?_, ?_⟩
    · obtain ⟨α⟩ := hS
      exact (h_nonneg α α).trans (le_sup' (fun ab : S × S ↦ h P ab.1 ab.2) (mem_univ (α, α)))
    · exact (sup'_lt_iff _).2 fun ab _ ↦ h_lt_one hP hP1 ab.1 ab.2
    · exact fun α β ↦ le_sup' (fun ab : S × S ↦ h P ab.1 ab.2) (mem_univ (α, β))

/-- p. 154: `Δ^{(i)} ≤ H Δ^{(i-1)}`, iterated: the values of `T^i f` lie in an interval of
length `H^i (M - m)`. -/
theorem iterate_spread [Nonempty S] (hP1 : ∀ α, ∑ γ, P α γ = 1) {H : ℝ}
    (hH : ∀ α β, h P α β ≤ H) (hH0 : 0 ≤ H) {f : S → ℝ} {m M : ℝ}
    (hf : ∀ γ, m ≤ f γ ∧ f γ ≤ M) (i : ℕ) :
    ∃ lo hi, (∀ α, lo ≤ (T P)^[i] f α ∧ (T P)^[i] f α ≤ hi) ∧ hi - lo ≤ H ^ i * (M - m) := by
  induction i with
  | zero => exact ⟨m, M, hf, by simp⟩
  | succ i ih =>
    obtain ⟨lo, hi, hb, hlen⟩ := ih
    set g := (T P)^[i] f
    have hspread : 0 ≤ hi - lo := by
      obtain ⟨α⟩ := (inferInstance : Nonempty S)
      linarith [(hb α).1, (hb α).2]
    obtain ⟨β, -, hβ⟩ := exists_mem_eq_inf' (univ_nonempty (α := S)) (T P g)
    refine ⟨T P g β, T P g β + H * (hi - lo), fun α ↦ ⟨?_, ?_⟩, ?_⟩
    · rw [Function.iterate_succ_apply', ← hβ]; exact inf'_le _ (mem_univ α)
    · rw [Function.iterate_succ_apply']
      have := T_sub_le hP1 hb α β
      have := mul_le_mul_of_nonneg_right (hH α β) hspread
      linarith
    · rw [pow_succ']
      have := mul_le_mul_of_nonneg_left hlen hH0
      linarith

/-- p. 154: all the `A^{(i)}_α` approach one limit `a`, and differ from it by at most
`C H^i` with `C = M - m`. -/
theorem iterate_tendsto [Nonempty S] (hP : ∀ α γ, 0 ≤ P α γ) (hP1 : ∀ α, ∑ γ, P α γ = 1)
    {H : ℝ} (hH : ∀ α β, h P α β ≤ H) (hH0 : 0 ≤ H) (hH1 : H < 1) {f : S → ℝ} {m M : ℝ}
    (hf : ∀ γ, m ≤ f γ ∧ f γ ≤ M) :
    ∃ a, ∀ i α, |(T P)^[i] f α - a| ≤ H ^ i * (M - m) := by
  have hstay : ∀ i lo hi, (∀ β, lo ≤ (T P)^[i] f β ∧ (T P)^[i] f β ≤ hi) →
      ∀ j β, lo ≤ (T P)^[i + j] f β ∧ (T P)^[i + j] f β ≤ hi := by
    intro i lo hi hb j
    induction j with
    | zero => exact hb
    | succ j ihj =>
      intro β
      rw [← add_assoc, Function.iterate_succ_apply']
      exact T_mem hP hP1 ihj β
  obtain ⟨α₀⟩ := (inferInstance : Nonempty S)
  set c : ℕ → ℝ := fun i ↦ (T P)^[i] f α₀
  have hstep : ∀ i, dist (c i) (c (i + 1)) ≤ (M - m) * H ^ i := by
    intro i
    obtain ⟨lo, hi, hb, hlen⟩ := iterate_spread hP1 hH hH0 hf i
    have h1 := hstay i lo hi hb 1 α₀
    rw [Real.dist_eq, abs_le]
    constructor <;> nlinarith [(hb α₀).1, (hb α₀).2]
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric H (M - m) hH1 hstep)
  refine ⟨a, fun i α ↦ ?_⟩
  obtain ⟨lo, hi, hb, hlen⟩ := iterate_spread hP1 hH hH0 hf i
  have hev : ∀ᶠ j in atTop, lo ≤ c j ∧ c j ≤ hi := eventually_atTop.2 ⟨i, fun j hj ↦ by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact hstay i lo hi hb k α₀⟩
  have hlo : lo ≤ a := ge_of_tendsto ha (hev.mono fun j hj ↦ hj.1)
  have hhi : a ≤ hi := le_of_tendsto ha (hev.mono fun j hj ↦ hj.2)
  rw [abs_le]
  constructor <;> linarith [(hb α).1, (hb α).2]

end Contraction

section Chain

variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- **The hypotheses of §5.** `X k` is the value (the label `α, β, γ, …`) taken by the `k`-th
quantity. Given the values of `x₀, …, x_k`, the probability that `x_{k+1} = γ` is `p_{α,γ}` when
`x_k = α`, independently of the earlier values and of `k`: the identity holds for every event
`E` determined by `x₀, …, x_k`. -/
structure IsChain (μ : Measure Ω) (X : ℕ → Ω → S) (P : S → S → ℝ) : Prop where
  measurable : ∀ k, Measurable (X k)
  markov : ∀ k (E : Set Ω), MeasurableSet[past X k] E → ∀ α γ,
    μ.real (E ∩ {ω | X k ω = α} ∩ {ω | X (k + 1) ω = γ}) =
      P α γ * μ.real (E ∩ {ω | X k ω = α})

namespace IsChain

variable {X : ℕ → Ω → S} {P : S → S → ℝ}

omit [Fintype S] in
theorem past_le (hc : IsChain μ X P) (k : ℕ) : past X k ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun j _ ↦ (hc.measurable j).comap_le

omit [Fintype S] in
theorem past_mono (X : ℕ → Ω → S) {k k' : ℕ} (hk : k ≤ k') : past X k ≤ past X k' :=
  iSup₂_le fun j hj ↦ le_iSup₂ (f := fun j (_ : j ∈ Set.Iic k') ↦
    MeasurableSpace.comap (X j) (inferInstance : MeasurableSpace S)) j
    (Set.mem_Iic.2 ((Set.mem_Iic.1 hj).trans hk))

omit [Fintype S] in
theorem measurableSet_eq (hc : IsChain μ X P) (k : ℕ) (α : S) :
    MeasurableSet {ω | X k ω = α} :=
  hc.measurable k (measurableSet_singleton α)

/-- Splitting an event according to the value of `x_k`. -/
theorem measureReal_eq_sum (hc : IsChain μ X P) {F : Set Ω} (hF : MeasurableSet F) (k : ℕ) :
    μ.real F = ∑ β, μ.real (F ∩ {ω | X k ω = β}) := by
  have hU : F = ⋃ β ∈ (univ : Finset S), F ∩ {ω | X k ω = β} := by
    ext ω; simp
  conv_lhs => rw [hU]
  refine measureReal_biUnion_finset ?_ fun β _ ↦ hF.inter (hc.measurableSet_eq k β)
  intro β _ γ _ hβγ
  refine Set.disjoint_left.2 fun ω h1 h2 ↦ hβγ ?_
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at h1 h2
  rw [← h1.2, h2.2]

/-- p. 152: `a_{k+i} = ∑ p^{(k)}_α A^{(i)}_α`, in the form needed below: for an event `E`
determined by `x₀, …, x_k` and any `f`,
`∑_γ P(E, x_{k+i} = γ) f γ = ∑_α P(E, x_k = α) (T^i f) α`. -/
theorem sum_prob_iterate (hc : IsChain μ X P) {k : ℕ} {E : Set Ω}
    (hE : MeasurableSet[past X k] E) (i : ℕ) (f : S → ℝ) :
    ∑ γ, μ.real (E ∩ {ω | X (k + i) ω = γ}) * f γ =
      ∑ α, μ.real (E ∩ {ω | X k ω = α}) * (T P)^[i] f α := by
  induction i generalizing f with
  | zero => simp
  | succ i ih =>
    have hE' : MeasurableSet[past X (k + i)] E := past_mono X (by omega) _ hE
    have hEm : MeasurableSet E := hc.past_le k _ hE
    rw [Function.iterate_succ_apply, ← ih (T P f)]
    have : ∀ γ, μ.real (E ∩ {ω | X (k + (i + 1)) ω = γ}) =
        ∑ β, P β γ * μ.real (E ∩ {ω | X (k + i) ω = β}) := by
      intro γ
      rw [hc.measureReal_eq_sum (hEm.inter (hc.measurableSet_eq _ γ)) (k + i)]
      refine sum_congr rfl fun β _ ↦ ?_
      rw [← hc.markov (k + i) E hE' β γ]
      congr 1; ext ω; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ← add_assoc]; tauto
    simp_rw [this, sum_mul, T, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun β _ ↦ sum_congr rfl fun γ _ ↦ by ring

theorem T_sub_const (hP1 : ∀ α, ∑ γ, P α γ = 1) (f : S → ℝ) (c : ℝ) (i : ℕ) :
    (T P)^[i] (fun γ ↦ f γ - c) = fun α ↦ (T P)^[i] f α - c := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext α
    simp only [T, mul_sub, sum_sub_distrib, ← sum_mul, hP1, one_mul]

theorem integral_comp (hc : IsChain μ X P) (k : ℕ) (φ : S → ℝ) :
    ∫ ω, φ (X k ω) ∂μ = ∑ α, μ.real {ω | X k ω = α} * φ α := by
  have : (fun ω ↦ φ (X k ω)) = fun ω ↦ ∑ α, φ α * {ω | X k ω = α}.indicator 1 ω := by
    funext ω
    rw [Fintype.sum_eq_single (X k ω) fun α hα ↦ by
      simp [Set.indicator, Ne.symm hα]]
    simp [Set.indicator]
  rw [this, integral_finsetSum univ (f := fun α ω ↦ φ α * {ω | X k ω = α}.indicator 1 ω)
    fun α _ ↦ by
      exact ((integrable_const (1 : ℝ)).indicator (hc.measurableSet_eq k α)).const_mul _]
  refine sum_congr rfl fun α _ ↦ ?_
  rw [integral_const_mul, integral_indicator_one (hc.measurableSet_eq k α), mul_comm]

theorem integral_mul_comp (hc : IsChain μ X P) (l k : ℕ) (φ ψ : S → ℝ) :
    ∫ ω, φ (X l ω) * ψ (X k ω) ∂μ =
      ∑ α, ∑ γ, μ.real ({ω | X l ω = α} ∩ {ω | X k ω = γ}) * (φ α * ψ γ) := by
  have hm : ∀ α γ, MeasurableSet ({ω | X l ω = α} ∩ {ω | X k ω = γ}) := fun α γ ↦
    (hc.measurableSet_eq l α).inter (hc.measurableSet_eq k γ)
  have : (fun ω ↦ φ (X l ω) * ψ (X k ω)) = fun ω ↦ ∑ α, ∑ γ,
      φ α * ψ γ * ({ω | X l ω = α} ∩ {ω | X k ω = γ}).indicator 1 ω := by
    funext ω
    rw [Fintype.sum_eq_single (X l ω) fun α hα ↦ by
      simp [Set.indicator, Ne.symm hα]]
    rw [Fintype.sum_eq_single (X k ω) fun γ hγ ↦ by
      simp [Set.indicator, Ne.symm hγ]]
    simp [Set.indicator]
  rw [this, integral_finsetSum univ (f := fun α ω ↦ ∑ γ,
      φ α * ψ γ * ({ω | X l ω = α} ∩ {ω | X k ω = γ}).indicator 1 ω)
    fun α _ ↦ by
      exact integrable_finsetSum _ fun γ _ ↦
        ((integrable_const (1 : ℝ)).indicator (hm α γ)).const_mul _]
  refine sum_congr rfl fun α _ ↦ ?_
  rw [integral_finsetSum univ (f := fun γ ω ↦
      φ α * ψ γ * ({ω | X l ω = α} ∩ {ω | X k ω = γ}).indicator 1 ω)
    fun γ _ ↦ by exact ((integrable_const (1 : ℝ)).indicator (hm α γ)).const_mul _]
  refine sum_congr rfl fun γ _ ↦ ?_
  rw [integral_const_mul, integral_indicator_one (hm α γ), mul_comm]

theorem sum_prob_eq_one (hc : IsChain μ X P) (k : ℕ) : ∑ α, μ.real {ω | X k ω = α} = 1 := by
  rw [← probReal_univ (μ := μ), hc.measureReal_eq_sum MeasurableSet.univ k]
  simp

/-- p. 152: `a_{l+i} = ∑_α p^{(l)}_α A^{(i)}_α`. -/
theorem integral_eq_sum_iterate (hc : IsChain μ X P) (v : S → ℝ) (l i : ℕ) :
    ∫ ω, v (X (l + i) ω) ∂μ = ∑ α, μ.real {ω | X l ω = α} * (T P)^[i] v α := by
  rw [hc.integral_comp]
  have := hc.sum_prob_iterate (k := l) (E := Set.univ) MeasurableSet.univ i v
  simpa using this

/-- The covariance of `x_l` and `x_{l+i}`:
`E z_l z_{l+i} = ∑_α p^{(l)}_α (α - a_l) (A^{(i)}_α - a_{l+i})`. -/
theorem cov_eq (hc : IsChain μ X P) (hP1 : ∀ α, ∑ γ, P α γ = 1) (v : S → ℝ) (l i : ℕ) :
    ∫ ω, (v (X l ω) - ∫ ω', v (X l ω') ∂μ) * (v (X (l + i) ω) - ∫ ω', v (X (l + i) ω') ∂μ) ∂μ
      = ∑ α, μ.real {ω | X l ω = α} * ((v α - ∫ ω', v (X l ω') ∂μ) *
          ((T P)^[i] v α - ∫ ω', v (X (l + i) ω') ∂μ)) := by
  set al := ∫ ω', v (X l ω') ∂μ
  set ak := ∫ ω', v (X (l + i) ω') ∂μ
  rw [hc.integral_mul_comp l (l + i) (fun α ↦ v α - al) (fun γ ↦ v γ - ak)]
  refine sum_congr rfl fun α _ ↦ ?_
  have hE : MeasurableSet[past X l] {ω | X l ω = α} :=
    measurableSet_past X le_rfl (measurableSet_singleton α)
  have h1 := hc.sum_prob_iterate hE i (fun γ ↦ v γ - ak)
  rw [T_sub_const hP1] at h1
  have h2 : ∑ β, μ.real ({ω | X l ω = α} ∩ {ω | X l ω = β}) * ((T P)^[i] v β - ak) =
      μ.real {ω | X l ω = α} * ((T P)^[i] v α - ak) := by
    rw [sum_eq_single α]
    · simp
    · intro β _ hβ
      have : {ω | X l ω = α} ∩ {ω | X l ω = β} = ∅ := by
        ext ω; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro h1 h2; exact hβ (h2 ▸ h1)
      simp [this]
    · simp
  rw [h2] at h1
  calc ∑ γ, μ.real ({ω | X l ω = α} ∩ {ω | X (l + i) ω = γ}) * ((v α - al) * (v γ - ak))
      = (v α - al) * ∑ γ, μ.real ({ω | X l ω = α} ∩ {ω | X (l + i) ω = γ}) * (v γ - ak) := by
        rw [mul_sum]; exact sum_congr rfl fun γ _ ↦ by ring
    _ = _ := by rw [h1]; ring

theorem wavg_mem {ι : Type*} [Fintype ι] {π g : ι → ℝ} (hπ : ∀ i, 0 ≤ π i) (hπ1 : ∑ i, π i = 1)
    {lo hi : ℝ} (hg : ∀ i, lo ≤ g i ∧ g i ≤ hi) : lo ≤ ∑ i, π i * g i ∧ ∑ i, π i * g i ≤ hi := by
  constructor
  · calc lo = ∑ i, π i * lo := by rw [← sum_mul, hπ1, one_mul]
      _ ≤ _ := sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hg i).1 (hπ i)
  · calc ∑ i, π i * g i ≤ ∑ i, π i * hi :=
          sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hg i).2 (hπ i)
      _ = hi := by rw [← sum_mul, hπ1, one_mul]

/-- p. 155: `|E z_l z_{l+i}| ≤ D H^i`, with `D = (M - m)²` where `m ≤ α ≤ M` for all values. -/
theorem abs_cov_le [Nonempty S] (hc : IsChain μ X P)
    (hP1 : ∀ α, ∑ γ, P α γ = 1) {H : ℝ} (hH : ∀ α β, h P α β ≤ H) (hH0 : 0 ≤ H)
    {v : S → ℝ} {m M : ℝ} (hv : ∀ α, m ≤ v α ∧ v α ≤ M) (l i : ℕ) :
    |∫ ω, (v (X l ω) - ∫ ω', v (X l ω') ∂μ) * (v (X (l + i) ω) - ∫ ω', v (X (l + i) ω') ∂μ) ∂μ|
      ≤ (M - m) ^ 2 * H ^ i := by
  rw [hc.cov_eq hP1 v l i]
  set π : S → ℝ := fun α ↦ μ.real {ω | X l ω = α}
  have hπ : ∀ α, 0 ≤ π α := fun α ↦ measureReal_nonneg
  have hπ1 : ∑ α, π α = 1 := hc.sum_prob_eq_one l
  have hal := wavg_mem hπ hπ1 hv
  rw [← hc.integral_comp l v] at hal
  obtain ⟨lo, hi, hb, hlen⟩ := iterate_spread hP1 hH hH0 hv i
  have hak := wavg_mem hπ hπ1 hb
  rw [← hc.integral_eq_sum_iterate v l i] at hak
  have hMm : 0 ≤ M - m := by
    obtain ⟨α⟩ := (inferInstance : Nonempty S); linarith [(hv α).1, (hv α).2]
  calc _ ≤ ∑ α, |π α * ((v α - ∫ ω', v (X l ω') ∂μ) *
          ((T P)^[i] v α - ∫ ω', v (X (l + i) ω') ∂μ))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ α, π α * ((M - m) * (H ^ i * (M - m))) := by
        refine sum_le_sum fun α _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (hπ α), abs_mul]
        refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_ (abs_nonneg _) hMm) (hπ α)
        · rw [abs_le]; constructor <;> linarith [(hv α).1, (hv α).2]
        · rw [abs_le]; constructor <;> linarith [(hb α).1, (hb α).2]
    _ = _ := by rw [← sum_mul, hπ1]; ring

/-- **§5, the law of large numbers for quantities linked in a chain.** If all the transition
probabilities `p_{α,γ}` are positive, the expectations `a_k` tend to a limit `a`, and for every
`ε > 0` the probability that `(x₁ + ⋯ + xₙ)/n` differs from `a` by at least `ε` tends to zero. -/
theorem lln (hc : IsChain μ X P) (hP : ∀ α γ, 0 < P α γ) (hP1 : ∀ α, ∑ γ, P α γ = 1)
    (v : S → ℝ) : ∃ a, Tendsto (fun k ↦ ∫ ω, v (X k ω) ∂μ) atTop (𝓝 a) ∧
      ∀ ε, 0 < ε → Tendsto (fun n : ℕ ↦
        μ.real {ω | ε ≤ |(∑ i ∈ range n, v (X i ω)) / n - a|}) atTop (𝓝 0) := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have : Nonempty S := ⟨X 0 (Classical.arbitrary Ω)⟩
  have hP0 : ∀ α γ, 0 ≤ P α γ := fun α γ ↦ (hP α γ).le
  obtain ⟨M, hM⟩ := Finite.exists_le v
  obtain ⟨m, hm⟩ := Finite.exists_ge v
  have hv : ∀ α, m ≤ v α ∧ v α ≤ M := fun α ↦ ⟨hm α, hM α⟩
  obtain ⟨H, hH0, hH1, hH⟩ := exists_H hP hP1
  obtain ⟨a, ha⟩ := iterate_tendsto hP0 hP1 hH hH0 hH1 hv
  have hmean : Tendsto (fun k ↦ ∫ ω, v (X k ω) ∂μ) atTop (𝓝 a) := by
    have hlim : Tendsto (fun k : ℕ ↦ H ^ k * (M - m)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hH0 hH1).mul_const (M - m)
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun k ↦ ?_) hlim)
    have := hc.integral_eq_sum_iterate v 0 k
    rw [zero_add] at this
    rw [this, Real.norm_eq_abs, ← one_mul a, ← hc.sum_prob_eq_one 0, sum_mul, ← sum_sub_distrib]
    calc _ ≤ ∑ α, |μ.real {ω | X 0 ω = α} * (T P)^[k] v α - μ.real {ω | X 0 ω = α} * a| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ α, μ.real {ω | X 0 ω = α} * (H ^ k * (M - m)) := by
          refine sum_le_sum fun α _ ↦ ?_
          rw [← mul_sub, abs_mul, abs_of_nonneg measureReal_nonneg]
          exact mul_le_mul_of_nonneg_left (ha k α) measureReal_nonneg
      _ = _ := by rw [← sum_mul, hc.sum_prob_eq_one 0, one_mul]
  refine ⟨a, hmean, fun ε hε ↦ ?_⟩
  have hL : ∀ i, MemLp (fun ω ↦ v (X i ω)) 2 μ := fun i ↦
    MemLp.of_bound ((Measurable.of_discrete (f := v)).comp (hc.measurable i)).aestronglyMeasurable
      (|m| + |M|) (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hv (X i ω), abs_nonneg m, abs_nonneg M, neg_abs_le m,
          le_abs_self M])
  refine lln_of_cov_decay (fun i ω ↦ v (X i ω)) hL (D := (M - m) ^ 2) hH0 hH1
    (fun k ↦ ?_) (fun l k hlk ↦ ?_) hmean hε
  · have := hc.abs_cov_le hP1 hH hH0 hv k 0
    simp only [add_zero, pow_zero, mul_one] at this
    simpa [sq] using (le_abs_self _).trans this
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hlk.le
    simpa using hc.abs_cov_le hP1 hH hH0 hv l i

end IsChain

end Chain

end SovietLean.Markov1906
