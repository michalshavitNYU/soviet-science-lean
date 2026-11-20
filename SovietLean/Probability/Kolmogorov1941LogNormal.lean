module

public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Kolmogorov (1941), *On the logarithmically normal law of distribution of particle sizes
under grinding*

Entry: `entries/probability/1941-kolmogorov-lognormal-grinding/`.

**The question.** Crushed rock, ore and sand show particle sizes whose *logarithms* are close
to normally distributed (data collected by N. K. Razumovsky, 1940). Kolmogorov explains why:
if particles break repeatedly, and each break shrinks a particle by a random factor whose law
does not depend on the particle's size, then sizes become asymptotically log-normal.

**The mechanism.** After `n` breaks a particle has size `rₙ = r₀ · k₁ ⋯ kₙ` with independent,
identically distributed ratios `kᵢ ∈ (0, 1]`. Taking logarithms turns the product into a sum,
`log(rₙ/r₀) = log k₁ + ⋯ + log kₙ`, and the central limit theorem makes the sum asymptotically
normal.

**Formal version.** We formalize this mechanism along one line of descent: size is measured in
units of the initial size (`r₀ = 1`), and the ratios are i.i.d. positive random variables with
`log kᵢ` square-integrable.

* `log_size_mean`, `log_size_variance`: the mean and variance of `log rₙ` grow linearly in `n`.
* `lognormal_limit`: `(log rₙ - n·m)/√n` converges in distribution to `N(0, v)`, where
  `m = E[log k]` and `v = Var[log k]`. That is, `rₙ` is asymptotically log-normal.

Kolmogorov's paper treats the whole population of fragments: he follows the expected number
of particles below each size in a continuous-time breakage process, and shows that their
log-sizes, suitably normalized, tend to a normal law. The lineage version here is the
probabilistic core of that argument; the population statement is open (see the entry's notes).

The central limit theorem is Mathlib's
(`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace SovietLean.Kolmogorov1941

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Size after `n` breaks, in units of the initial size: `rₙ = k₀ ⋯ k_{n-1}`. -/
noncomputable def size (k : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∏ i ∈ range n, k i ω

omit [MeasurableSpace Ω] in
/-- The logarithm turns the product of ratios into a sum. -/
theorem log_size (k : ℕ → Ω → ℝ) (hpos : ∀ i ω, 0 < k i ω) (n : ℕ) (ω : Ω) :
    Real.log (size k n ω) = ∑ i ∈ range n, Real.log (k i ω) :=
  Real.log_prod (fun i _ ↦ (hpos i ω).ne')

/-- **Mean of the log-size grows linearly**: `E[log rₙ] = n · E[log k]`. -/
theorem log_size_mean (k : ℕ → Ω → ℝ) (hpos : ∀ i ω, 0 < k i ω)
    (hident : ∀ i, IdentDistrib (k i) (k 0) P P)
    (hint : Integrable (fun ω ↦ Real.log (k 0 ω)) P) (n : ℕ) :
    ∫ ω, Real.log (size k n ω) ∂P = n * ∫ ω, Real.log (k 0 ω) ∂P := by
  have hid : ∀ i, IdentDistrib (fun ω ↦ Real.log (k i ω)) (fun ω ↦ Real.log (k 0 ω)) P P :=
    fun i ↦ (hident i).comp Real.measurable_log
  simp_rw [log_size k hpos]
  rw [integral_finsetSum _ fun i _ ↦ (hid i).integrable_iff.2 hint]
  simp [fun i ↦ (hid i).integral_eq]

/-- **Variance of the log-size grows linearly**: `Var[log rₙ] = n · Var[log k]`. -/
theorem log_size_variance (k : ℕ → Ω → ℝ) (hpos : ∀ i ω, 0 < k i ω)
    (hind : iIndepFun k P) (hident : ∀ i, IdentDistrib (k i) (k 0) P P)
    (hL2 : MemLp (fun ω ↦ Real.log (k 0 ω)) 2 P) (n : ℕ) :
    Var[fun ω ↦ Real.log (size k n ω); P] = n * Var[fun ω ↦ Real.log (k 0 ω); P] := by
  have hid : ∀ i, IdentDistrib (fun ω ↦ Real.log (k i ω)) (fun ω ↦ Real.log (k 0 ω)) P P :=
    fun i ↦ (hident i).comp Real.measurable_log
  have hind' : iIndepFun (fun i ω ↦ Real.log (k i ω)) P :=
    hind.comp (fun _ x ↦ Real.log x) (fun _ ↦ Real.measurable_log)
  have heq : (fun ω ↦ Real.log (size k n ω)) = ∑ i ∈ range n, fun ω ↦ Real.log (k i ω) := by
    funext ω; simp [log_size k hpos, Finset.sum_apply]
  rw [heq, IndepFun.variance_sum (fun i _ ↦ (hid i).memLp_iff.2 hL2)
    (fun i _ j _ hij ↦ hind'.indepFun hij)]
  simp [fun i ↦ (hid i).variance_eq]

/-- **Kolmogorov's log-normal law** (lineage form). If a particle breaks repeatedly by
independent, identically distributed ratios `kᵢ > 0` with `log kᵢ` square-integrable, then
`(log rₙ - n·E[log k]) / √n` converges in distribution to a centred normal law with variance
`Var[log k]`. -/
theorem lognormal_limit [IsProbabilityMeasure P] {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : Ω' → ℝ}
    (k : ℕ → Ω → ℝ) (hpos : ∀ i ω, 0 < k i ω)
    (hind : iIndepFun k P) (hident : ∀ i, IdentDistrib (k i) (k 0) P P)
    (hL2 : MemLp (fun ω ↦ Real.log (k 0 ω)) 2 P)
    (hY : HasLaw Y (gaussianReal 0 Var[fun ω ↦ Real.log (k 0 ω); P].toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ * (Real.log (size k n ω) - n * ∫ ω, Real.log (k 0 ω) ∂P))
      atTop Y (fun _ ↦ P) P' := by
  have hid : ∀ i, IdentDistrib (fun ω ↦ Real.log (k i ω)) (fun ω ↦ Real.log (k 0 ω)) P P :=
    fun i ↦ (hident i).comp Real.measurable_log
  have hind' : iIndepFun (fun i ω ↦ Real.log (k i ω)) P :=
    hind.comp (fun _ x ↦ Real.log x) (fun _ ↦ Real.measurable_log)
  simp_rw [log_size k hpos]
  exact tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun i ω ↦ Real.log (k i ω)) hY hL2
    hind' hid

end SovietLean.Kolmogorov1941
