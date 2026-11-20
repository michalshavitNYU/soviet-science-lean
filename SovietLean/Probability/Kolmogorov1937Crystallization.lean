module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Kolmogorov (1937), *On the statistical theory of the crystallization of metals*

Entry: `entries/probability/1937-kolmogorov-crystallization/`.

**The model (§1).** A volume `V` is filled at `t = 0` by the parent phase. In the part not yet
crystallized, new centres of crystallization appear at random: in any free volume `V'` one
centre appears during `(t, t + Δt)` with probability `α(t) V' Δt + o(Δt)`, and more than one
with probability `o(Δt)`, independently of the past. Around every centre the crystal grows with
linear speed `c(t, n) = k(t) c(n)`, the same law at every point.

**The result (§2).** A point `P` is still uncrystallized at time `t` iff no centre has appeared
at any earlier time `t'` within distance `c(n) ∫_{t'}^t k` of `P`. These points fill, at time
`t'`, a volume `V'(t') = (4π/3) c³ (∫_{t'}^t k)³`, where `c³` is the mean of `c(n)³` over the
unit sphere. Multiplying the "no centre" probabilities over small time steps (eq. (1)) and
taking logarithms (eq. (2)), Kolmogorov obtains the probability that `P` is crystallized:

  `p(t) = 1 - exp(-(4π/3) c³ Ω)`, `Ω = ∫₀ᵗ α(t') (∫_{t'}^t k(τ) dτ)³ dt'`.   (3), (4)

**§3.** For constant `α` and `k = 1`, `Ω = α t⁴/4` (4a), so `V₁(t) = V(1 - exp(-(π/3) c³ α t⁴))`
(5a). The number of centres is `N(t) = V ∫₀ᵗ α(τ) q(τ) dτ` (6); for constant data the
substitution `ξ = (π c³ α/3)^{1/4} τ` gives (6a), and as `t → ∞` the total number (7a). If all
centres appear at `t = 0`, `β` per unit volume, then `Ω = β (∫₀ᵗ k)³` (4b) and, for `k = 1`,
`Ω = β t³` (4c), `V₁(t) = V(1 - exp(-(4π/3) c³ β t³))` (5c).

## Formal version

| Paper | Lean | Status |
|---|---|---|
| (4) ⇒ (4a): `Ω = α t⁴/4` for constant `α`, `k = 1` | `Omega_const` | proved |
| same integral in dimension `d`, growth speed `v` | `nucleation_integral_dim` | proved |
| (3), (4a) ⇒ (5a): exponent `(π/3) c³ α t⁴` | `crystallized_const` | proved |
| (4c), (5c): nucleation at `t = 0` only | `Omega_instant_one`, `crystallized_instant` | proved |
| `1 - exp(-a tⁿ)` is `0` at `t = 0` | `fraction_zero` | proved |
| `1 - exp(-a tⁿ)` is nondecreasing | `fraction_monotoneOn` | proved |
| `1 - exp(-a tⁿ) → 1` | `fraction_tendsto_one` | proved |
| (6) ⇒ (6a): the substitution `ξ = λ τ` | `count_substitution` | proved |
| (7a): `N(+∞) = V (3α³/(π c³))^{1/4} Γ(5/4)` | `total_count` | proved |
| Poisson void probability `exp(-Ω)` | `void_prob`, `uncrystallized_prob` | proved |
| independent regions: void probabilities multiply | `void_prob_add` | proved |
| (1) ⇒ (2): the product limit `∏(1 - α V' Δt') → exp(-∫ α V')` | — | open |

Notes on matching the source.

* The paper derives the Poisson structure from the infinitesimal hypothesis of §1 via the
  product (1). We do not formalize that limit. Instead, `void_prob` and `uncrystallized_prob`
  take as hypothesis what the limit produces: the number of centres in the relevant space-time
  region ("the cone" of points `P'` at times `t'`) is Poisson with mean `(4π/3) c³ Ω`. Then the
  probability of no centre, i.e. that `P` is not yet crystallized, is `exp(-(4π/3) c³ Ω)`.
* `Ω` is defined with interval integrals of arbitrary real functions `α`, `k`; for the explicit
  cases (4a), (4c) no integrability hypotheses are needed.
* `total_count` is (7a) in exact form, with Mathlib's `∫₀^∞ exp(-b x^p) = b^{-1/p} Γ(1/p + 1)`
  (`integral_exp_neg_mul_rpow`). The paper's numerical value `~ 0.9 V (α/c)^{4/3}` is printed with
  the exponent `4/3`; the exact formula gives `(α/c)^{3/4}` (see the entry's notes). We do not
  formalize the numerical constant `(3/π)^{1/4} Γ(5/4) ≈ 0.89`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology NNReal

namespace SovietLean.Kolmogorov1937

/-- Eq. (4): `Ω(t) = ∫₀ᵗ α(t') (∫_{t'}^t k(τ) dτ)³ dt'`. -/
noncomputable def Omega (α k : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ t' in (0 : ℝ)..t, α t' * (∫ τ in t'..t, k τ) ^ 3

/-- Eq. (3): the probability that a given point is crystallized at time `t`,
`p(t) = 1 - exp(-(4π/3) c³ Ω)`. -/
noncomputable def crystallized (c : ℝ) (α k : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 - exp (-(4 * π / 3) * c ^ 3 * Omega α k t)

/-- Eq. (4b): nucleation only at `t = 0`, `β` centres per unit volume: `Ω = β (∫₀ᵗ k)³`. -/
noncomputable def OmegaInstant (β : ℝ) (k : ℝ → ℝ) (t : ℝ) : ℝ :=
  β * (∫ τ in (0 : ℝ)..t, k τ) ^ 3

/-- The time integral behind (4a), in any dimension `d`: with nucleation rate `I`, growth
speed `v` and `c_d` the volume of the unit ball,
`∫₀ᵗ I c_d (v (t - s))^d ds = I c_d v^d t^{d+1}/(d+1)`. For `d = 3`, `c_3 = 4π/3`, this is
`(π/3) I v³ t⁴`. -/
theorem nucleation_integral_dim (I C v t : ℝ) (d : ℕ) :
    ∫ s in (0 : ℝ)..t, I * C * (v * (t - s)) ^ d = I * C * v ^ d * t ^ (d + 1) / (d + 1) := by
  simp_rw [mul_pow, ← mul_assoc]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left
    (fun x ↦ x ^ d), integral_pow]
  simp
  ring

/-- Eq. (4a): for constant `α` and `k = 1`, `Ω = α t⁴ / 4`. -/
theorem Omega_const (α t : ℝ) : Omega (fun _ ↦ α) (fun _ ↦ 1) t = α * t ^ 4 / 4 := by
  have h := nucleation_integral_dim α 1 1 t 3
  simp only [mul_one, one_mul, one_pow] at h
  simp only [Omega, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  rw [h]; norm_num

/-- Eq. (5a): for constant `α` and `k = 1`, `p(t) = 1 - exp(-(π/3) c³ α t⁴)`. -/
theorem crystallized_const (c α t : ℝ) :
    crystallized c (fun _ ↦ α) (fun _ ↦ 1) t = 1 - exp (-(π / 3) * c ^ 3 * α * t ^ 4) := by
  rw [crystallized, Omega_const]
  congr 2
  ring

/-- Eq. (4c): nucleation at `t = 0` only, `k = 1`: `Ω = β t³`. -/
theorem Omega_instant_one (β t : ℝ) : OmegaInstant β (fun _ ↦ 1) t = β * t ^ 3 := by
  simp [OmegaInstant]

/-- Eq. (5c): `p(t) = 1 - exp(-(4π/3) c³ β t³)`. -/
theorem crystallized_instant (c β t : ℝ) :
    1 - exp (-(4 * π / 3) * c ^ 3 * OmegaInstant β (fun _ ↦ 1) t) =
      1 - exp (-(4 * π / 3) * c ^ 3 * β * t ^ 3) := by
  rw [Omega_instant_one, mul_assoc _ β]

/-! ### The crystallized fraction `1 - exp(-a tⁿ)`

Both (5a) (`n = 4`, `a = (π/3) c³ α`) and (5c) (`n = 3`, `a = (4π/3) c³ β`) have this form. -/

/-- At `t = 0` nothing is crystallized. -/
theorem fraction_zero (a : ℝ) {n : ℕ} (hn : n ≠ 0) : 1 - exp (-a * 0 ^ n) = 0 := by
  simp [hn]

/-- The crystallized fraction is nondecreasing in time. -/
theorem fraction_monotoneOn {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    MonotoneOn (fun t : ℝ ↦ 1 - exp (-a * t ^ n)) (Ici 0) := by
  intro s hs t _ hst
  have : s ^ n ≤ t ^ n := pow_le_pow_left₀ hs hst n
  have : -a * t ^ n ≤ -a * s ^ n := by nlinarith
  dsimp only
  linarith [exp_le_exp.2 this]

/-- Eventually everything crystallizes: the fraction tends to `1`. -/
theorem fraction_tendsto_one {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun t : ℝ ↦ 1 - exp (-a * t ^ n)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun t : ℝ ↦ a * t ^ n) atTop atTop :=
    (tendsto_pow_atTop hn).const_mul_atTop ha
  have h2 := tendsto_exp_neg_atTop_nhds_zero.comp h1
  simpa [Function.comp_def, neg_mul] using h2.const_sub (1 : ℝ)

/-! ### The number of centres, (6a) and (7a) -/

/-- Eq. (6) ⇒ (6a), the substitution `ξ = λ τ` with `λ⁴ = π c³ α / 3`:
`∫₀ᵗ exp(-λ⁴ τ⁴) dτ = λ⁻¹ ∫₀^{λ t} exp(-ξ⁴) dξ`. -/
theorem count_substitution {l : ℝ} (hl : l ≠ 0) (t : ℝ) :
    ∫ τ in (0 : ℝ)..t, exp (-(l ^ 4 * τ ^ 4)) = l⁻¹ * ∫ ξ in (0 : ℝ)..l * t, exp (-ξ ^ 4) := by
  have := intervalIntegral.integral_comp_mul_left (fun ξ ↦ exp (-ξ ^ 4)) hl
    (a := 0) (b := t)
  simp only [mul_zero, smul_eq_mul] at this
  rw [← this]
  congr 1; funext τ; rw [mul_pow]

/-- Eq. (7a), exact form: with constant `α > 0`, `c > 0`, `k = 1`, the number of centres
`N(t) = V α ∫₀ᵗ exp(-(π/3) c³ α τ⁴) dτ` tends, as `t → ∞`, to
`V (3α³/(π c³))^{1/4} Γ(5/4)`, where `Γ(5/4) = ∫₀^∞ e^{-ξ⁴} dξ`. -/
theorem total_count (V : ℝ) {α c : ℝ} (hα : 0 < α) (hc : 0 < c) :
    Tendsto (fun t ↦ V * α * ∫ τ in (0 : ℝ)..t, exp (-(π / 3) * c ^ 3 * α * τ ^ 4)) atTop
      (𝓝 (V * (3 * α ^ 3 / (π * c ^ 3)) ^ (4⁻¹ : ℝ) * Gamma (1 / 4 + 1))) := by
  set b := π / 3 * c ^ 3 * α with hb_def
  have hb : 0 < b := by positivity
  have hfun : (fun τ : ℝ ↦ exp (-(π / 3) * c ^ 3 * α * τ ^ 4)) =
      fun τ ↦ exp (-b * τ ^ (4 : ℝ)) := by
    funext τ; rw [rpow_ofNat, hb_def]; ring_nf
  have hint : IntegrableOn (fun τ : ℝ ↦ exp (-b * τ ^ (4 : ℝ))) (Ioi 0) := by
    simpa using
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (p := 4) (by norm_num) (by norm_num) hb
  have hlim := (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id).const_mul (V * α)
  rw [integral_exp_neg_mul_rpow (by norm_num) hb] at hlim
  -- `α b^{-1/4} = (3α³/(π c³))^{1/4}`
  have hα4 : α = (α ^ 4) ^ (4⁻¹ : ℝ) := by
    rw [show (4⁻¹ : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num, pow_rpow_inv_natCast hα.le (by norm_num)]
  have key : 3 * α ^ 3 / (π * c ^ 3) = α ^ 4 / b := by
    rw [hb_def]; field_simp
  have hval : V * (3 * α ^ 3 / (π * c ^ 3)) ^ (4⁻¹ : ℝ) * Gamma (1 / 4 + 1) =
      V * α * (b ^ (-1 / 4 : ℝ) * Gamma (1 / 4 + 1)) := by
    rw [key, div_rpow (by positivity) hb.le, ← hα4, show (-1 / 4 : ℝ) = -(4⁻¹ : ℝ) by norm_num,
      rpow_neg hb.le]
    ring
  rw [hfun, hval]
  exact hlim

/-! ### The Poisson void probability behind `exp(-Ω)` -/

variable {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'}

/-- If the number `X` of centres in a region is Poisson with mean `r`, the probability that the
region contains no centre is `exp(-r)`. -/
theorem void_prob {X : Ω' → ℕ} {r : ℝ≥0} (hX : HasLaw X Po(r) P) :
    P.real {ω | X ω = 0} = exp (-(r : ℝ)) := by
  have hm : P.real (X ⁻¹' {0}) = (P.map X).real {0} := by
    rw [measureReal_def, measureReal_def,
      Measure.map_apply_of_aemeasurable hX.aemeasurable (measurableSet_singleton 0)]
  rw [show {ω | X ω = 0} = X ⁻¹' {0} from rfl, hm, hX.map_eq, poissonMeasure_real_singleton]
  simp

/-- Eq. (3) in Poisson form: if the number of centres in the space-time region that would
already cover `P` is Poisson with mean `(4π/3) c³ Ω`, the probability that `P` is not yet
crystallized is `q(t) = exp(-(4π/3) c³ Ω) = 1 - p(t)`. -/
theorem uncrystallized_prob (c : ℝ) (α k : ℝ → ℝ) (t : ℝ) {X : Ω' → ℕ} {r : ℝ≥0}
    (hr : (r : ℝ) = 4 * π / 3 * c ^ 3 * Omega α k t) (hX : HasLaw X Po(r) P) :
    P.real {ω | X ω = 0} = 1 - crystallized c α k t := by
  rw [void_prob hX, crystallized, hr]
  ring_nf

/-- Disjoint parts of the region contribute independent Poisson counts, and the void
probabilities multiply: `P(no centre) = exp(-r₁) exp(-r₂)`. This is the multiplicativity used
in the product (1). -/
theorem void_prob_add {X Y : Ω' → ℕ} {r₁ r₂ : ℝ≥0} (hXY : IndepFun X Y P)
    (hX : HasLaw X Po(r₁) P) (hY : HasLaw Y Po(r₂) P) :
    P.real {ω | X ω + Y ω = 0} = exp (-(r₁ : ℝ)) * exp (-(r₂ : ℝ)) := by
  have := void_prob (IndepFun.hasLaw_add_poissonMeasure hXY hX hY)
  simp only [Pi.add_apply, NNReal.coe_add] at this
  rw [this, ← exp_add]; ring_nf

end SovietLean.Kolmogorov1937
