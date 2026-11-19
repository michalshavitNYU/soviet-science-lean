module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Kolmogorov (1928), *Über die Summen durch den Zufall bestimmter unabhängiger Größen*

Entry: `entries/probability/1928-kolmogorov-summen/`.

**Kolmogorov's maximal inequality.** Let `X₀, …, Xₙ` be independent, square-integrable,
mean-zero random variables and `Sₖ = X₀ + ⋯ + Xₖ`. For every `ε > 0`,
`P(max_{k ≤ n} |Sₖ| ≥ ε) ≤ (Var X₀ + ⋯ + Var Xₙ) / ε²`.

Compared with Chebyshev's inequality for `Sₙ` alone, the bound is the same but the
event is much larger: it controls the whole path `S₀, …, Sₙ`.

**Status: statement only.** The proof is left as `sorry`; this is an open task for
contributors (one route: `Sₖ²` is a submartingale, then Doob's `MeasureTheory.maximal_ineq`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SovietScience.Kolmogorov1928

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Partial sums `S k = X 0 + ⋯ + X k`. -/
def partialSum (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), X i ω

/-- **Kolmogorov's maximal inequality.** -/
theorem maximal_inequality (X : ℕ → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hind : iIndepFun X μ) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ |partialSum X k ω|)}
      ≤ (∑ i ∈ Finset.range (n + 1), variance (X i) μ) / ε ^ 2 := by
  sorry

end SovietScience.Kolmogorov1928
