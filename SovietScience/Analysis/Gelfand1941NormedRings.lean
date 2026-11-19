module

public import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Gelfand (1941), *Normierte Ringe*

Entry: `entries/analysis/1941-gelfand-normierte-ringe/`.

Gelfand's paper founds the theory of commutative Banach algebras ("normed rings"). This file
formalizes three of its basic results for a complex Banach algebra `A` with unit.

1. **The spectrum is nonempty.** Every element `a` has some `λ ∈ ℂ` with `a - λ·1` not
   invertible. (Gelfand's argument: otherwise the resolvent `λ ↦ (a - λ·1)⁻¹` would be a
   bounded entire function vanishing at infinity, hence zero, which is impossible.)
2. **Spectral radius formula.** `max {|λ| : λ ∈ σ(a)} = lim ‖aⁿ‖^{1/n}`.
3. **Gelfand–Mazur.** If every nonzero element of `A` is invertible, then `A = ℂ·1`.
   (Announced by Mazur in 1938 without proof; Gelfand's paper gives a proof.)

**Formal version.** "Normed ring" becomes `[NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]`.
Gelfand assumes `‖e‖ = 1` for the unit; Mathlib does not (that is the separate class
`NormOneClass`), and none of the results below need it.
The spectral radius is `spectralRadius ℂ a : ℝ≥0∞`, the supremum of `‖λ‖` over the spectrum,
and the limit is taken in `ℝ≥0∞`. Gelfand–Mazur is stated as: each `a` equals `z·1` for a
unique `z ∈ ℂ`.

Proofs are Mathlib's (`Mathlib.Analysis.Normed.Algebra.GelfandFormula`; see that file for its
authors); this file records the match with the source.
-/

@[expose] public section

open Filter Topology
open scoped NNReal ENNReal

namespace SovietScience.Gelfand1941

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **The spectrum of every element of a nonzero complex Banach algebra is nonempty.** -/
theorem spectrum_nonempty [Nontrivial A] (a : A) : (spectrum ℂ a).Nonempty :=
  spectrum.nonempty a

/-- **Gelfand's spectral radius formula**: `r(a) = lim_{n→∞} ‖aⁿ‖^{1/n}`. -/
theorem spectral_radius_formula (a : A) :
    Tendsto (fun n : ℕ ↦ (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) atTop (𝓝 (spectralRadius ℂ a)) :=
  spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a

/-- **Gelfand–Mazur theorem**: a complex Banach algebra in which every nonzero element is
invertible is `ℂ` itself: every element is `z • 1` for exactly one complex number `z`. -/
theorem gelfand_mazur (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0) (a : A) :
    ∃! z : ℂ, algebraMap ℂ A z = a :=
  (NormedRing.algEquivComplexOfComplete hA).bijective.existsUnique a

end SovietScience.Gelfand1941
