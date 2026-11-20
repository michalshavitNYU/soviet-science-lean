module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Darboux
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Friedmann (1922), *Über die Krümmung des Raumes*

Entry: `entries/high-energy/1922-friedmann-kruemmung-des-raumes/`.

**Setting.** Friedmann looks for solutions of Einstein's equations with cosmological term,
(A), for incoherent matter at rest, (C), in a world whose space has constant positive curvature
that may depend on time. With time orthogonal to space and `M = 1` the line element is

  `dτ² = -(R(x₄)²/c²) (dx₁² + sin²x₁ dx₂² + sin²x₁ sin²x₂ dx₃²) + dx₄²`.   (D₃)

The field equations then reduce (§2, no. 2) to two ordinary differential equations for the
"radius of curvature" `R(t)` (Friedmann writes `t` for `x₄`, `R' = dR/dx₄`):

  `R'²/R² + 2RR''/R² + c²/R² - λ = 0`,          (4)  [(A) with `i = k = 1, 2, 3`]
  `3R'²/R² + 3c²/R² - λ = κ c² ρ`,              (5)  [(A) with `i = k = 4`]

and integrating (4) gives

  `(1/c²) (dR/dt)² = (A - R + (λ/(3c²)) R³) / R`,  `A` an arbitrary constant.   (6)

From (5) and (6), `ρ = 3A/(κR³)` (8), and with the total mass `M̄` of space, `A = κM̄/(6π²)` (9).
In §1 he recovers Einstein's static cylinder world, `λ = c²/R²`, `ρ = 2/(κR²)`, `M̄ = 4π²R/κ`.
In §2, nos. 3–6, he classifies the non-stationary worlds by the positive roots of
`A - x + (λ/(3c²)) x³ = 0`: the curves `y x³ - x + A = 0` (10) have their maximum at
`x = 3A/2, y = 4/(27A²)`, which gives the critical value `λ₁ = 4c²/(9A²)`. For `λ > λ₁` the
world is *monotonic of the first kind*; for `λ < 0` the radius oscillates between `0` and the
root `x₀ ∈ (0, A)`: the *periodic world*, with period `t_π` (14); for small `λ`, `t_π ≈ πA/c` (15).

**What is not formalized.** Mathlib has no Lorentzian geometry, so the reduction of Einstein's
equations (A)–(D₃) to (4), (5) is not formalized. We take (4), (5), (6) as Friedmann writes them,
as relations between the numbers `R, R', R''` at a time `t`, and prove what follows from them.
Lean reserves the letter `λ`, so the cosmological constant is called `lam`; `κ` is Einstein's
constant. Nothing is rescaled: `c`, `κ`, `λ`, `A` are kept as in the paper.

## Formal version

| Paper | Lean | Status |
|---|---|---|
| (4) ⇒ (6): `R R'² + c²R - (λ/3) R³` has derivative `0` | `energy_hasDerivAt` | proved |
| (4) ⇒ (6): the first integral, `= c²A` | `eq6_of_eq4` | proved |
| (6) ⇒ (4) where `R' ≠ 0` (the converse, "Da R' nicht = 0 ist") | `eq4_of_eq6` | proved |
| (5), (6) ⇒ (8): `ρ = 3A/(κR³)` | `density_eq` | proved |
| the volume of space is `2π²R³` (used for `M̄`) | `volume_of_space` | proved |
| (8) ⇒ (9): `A = κM̄/(6π²)`; `A > 0` iff `M̄ > 0` | `A_eq_mass`, `A_pos_iff` | proved |
| §2.1: static world: (4) with `R' = R'' = 0` iff `λ = c²/R²` | `static_eq4_iff` | proved |
| §2.1: then `ρ = 2/(κR²)`, `M̄ = 4π²R/κ` (Einstein) | `static_density`, `static_mass` | proved |
| (10): `(x - A)/x³ ≤ 4/(27A²)` | `cubic_max` | proved |
| (10): equality only at `x = 3A/2` | `cubic_max_eq_iff` | proved |
| §2.4: for `λ > λ₁` the radicand of (7) has no positive root | `radicand_pos` | proved |
| §2.4: hence the world is monotonic (`R` strictly monotone) | `monotonic_world` | proved |
| §2.3: for `λ < 0` there is a root `x₀ ∈ (0, A)` | `exists_root_of_neg` | proved |
| §2.6, `λ = 0`: an explicit periodic solution of (6) (cycloid) | `periodicWorld_eq6` | proved |
| ... `R = 0` at `t = 0` | `periodicWorld_zero` | proved |
| ... `R = 0` again at `t = πA/c`, (15) | `periodicWorld_period` | proved |
| ... maximum `A` at `t = πA/(2c)` | `periodicWorld_half` | proved |
| ... period `πA/c`, (15) | `periodicWorld_periodic` | proved |
| ... `0 ≤ R ≤ A` | `periodicWorld_le` | proved |

Notes on matching the source.

* (4), (5), (6) are stated as Friedmann prints them, with divisions. Hypotheses `R ≠ 0`,
  `c ≠ 0`, `κ ≠ 0` are made explicit where the paper divides by these quantities.
* Derivatives are `HasDerivAt`: `R'` is the derivative of `R`, `R''` that of `R'`. The first
  integral is proved on a closed time interval on which `R ≠ 0`.
* The total mass is *defined* as `M̄ = 2π²R³ρ`, density times the volume of space; that this
  volume is `2π²R³` for the metric (D₃) (spatial line element `R²(dx₁² + ...)` in the units of
  `ds`) is proved separately as an iterated integral over Friedmann's coordinate ranges (§1.4).
* For `λ = 0` Friedmann writes no closed form; the solution of (7) is the cycloid
  `R = (A/2)(1 - cos η)`, `t = (A/(2c))(η - sin η)`. We define `R(t)` by inverting
  `η ↦ η - sin η` and prove (6) at every `t` with `R(t) ≠ 0`. Its period `πA/c` is exactly
  Friedmann's (15); for `λ = 0` the approximation (15) is an equality.
-/

@[expose] public section

open Real Set Filter
open scoped Topology

namespace SovietLean.Friedmann1922

/-! ### The equations (4), (5), (6) -/

/-- Eq. (4): `R'²/R² + 2RR''/R² + c²/R² - λ = 0`, the equations (A) with `i = k = 1, 2, 3`. -/
def eq4 (c lam R R' R'' : ℝ) : Prop :=
  R' ^ 2 / R ^ 2 + 2 * R * R'' / R ^ 2 + c ^ 2 / R ^ 2 - lam = 0

/-- Eq. (5): `3R'²/R² + 3c²/R² - λ = κc²ρ`, the equation (A) with `i = k = 4`. -/
def eq5 (κ c lam ρ R R' : ℝ) : Prop :=
  3 * R' ^ 2 / R ^ 2 + 3 * c ^ 2 / R ^ 2 - lam = κ * c ^ 2 * ρ

/-- Eq. (6): `(1/c²)(dR/dt)² = (A - R + (λ/(3c²)) R³)/R`. -/
def eq6 (c lam A R R' : ℝ) : Prop :=
  1 / c ^ 2 * R' ^ 2 = (A - R + lam / (3 * c ^ 2) * R ^ 3) / R

/-- The quantity `R R'² + c² R - (λ/3) R³`, which (4) keeps constant; it equals `c² A`. -/
noncomputable def energy (c lam : ℝ) (R R' : ℝ → ℝ) (s : ℝ) : ℝ :=
  R s * R' s ^ 2 + c ^ 2 * R s - lam / 3 * R s ^ 3

/-- Along a solution of (4), the quantity `R R'² + c²R - (λ/3)R³` has derivative zero. -/
theorem energy_hasDerivAt {R R' : ℝ → ℝ} {R'' c lam t : ℝ}
    (h1 : HasDerivAt R (R' t) t) (h2 : HasDerivAt R' R'' t) (hR : R t ≠ 0)
    (h4 : eq4 c lam (R t) (R' t) R'') :
    HasDerivAt (energy c lam R R') 0 t := by
  have h := ((h1.mul (h2.pow 2)).add (h1.const_mul (c ^ 2))).sub ((h1.pow 3).const_mul (lam / 3))
  unfold energy
  convert h using 1
  unfold eq4 at h4
  field_simp at h4
  simp only [Pi.pow_apply]
  push_cast
  linear_combination (-(R' t)) * h4

/-- (4) ⇒ (6), "die Integration der Gleichung (4)": on a time interval where `R ≠ 0`, every
solution of (4) satisfies (6) with the constant `A = (R R'² + c²R - (λ/3)R³)/c²`. -/
theorem eq6_of_eq4 {R R' R'' : ℝ → ℝ} {c lam a b : ℝ} (hc : c ≠ 0)
    (hR : ∀ s ∈ Icc a b, R s ≠ 0)
    (h1 : ∀ s ∈ Icc a b, HasDerivAt R (R' s) s)
    (h2 : ∀ s ∈ Icc a b, HasDerivAt R' (R'' s) s)
    (h4 : ∀ s ∈ Icc a b, eq4 c lam (R s) (R' s) (R'' s)) :
    ∀ s ∈ Icc a b, eq6 c lam (energy c lam R R' a / c ^ 2) (R s) (R' s) := by
  have hd : ∀ s ∈ Icc a b, HasDerivAt (energy c lam R R') 0 s := fun s hs ↦
    energy_hasDerivAt (h1 s hs) (h2 s hs) (hR s hs) (h4 s hs)
  have hconst := constant_of_has_deriv_right_zero
    (fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs ↦ (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
  intro s hs
  have hE := hconst s hs
  have hRs := hR s hs
  unfold eq6
  rw [← hE]
  unfold energy
  field_simp
  ring

/-- (6) ⇒ (4) where `R' ≠ 0`: differentiating (6) gives back (4). This is why Friedmann notes
`R' ≠ 0` before integrating. -/
theorem eq4_of_eq6 {R R' : ℝ → ℝ} {R'' c lam A t : ℝ} (hc : c ≠ 0) (hR' : R' t ≠ 0)
    (h1 : HasDerivAt R (R' t) t) (h2 : HasDerivAt R' R'' t)
    (h6 : ∀ᶠ s in 𝓝 t, R s ≠ 0 ∧ eq6 c lam A (R s) (R' s)) :
    eq4 c lam (R t) (R' t) R'' := by
  have hRt : R t ≠ 0 := h6.self_of_nhds.1
  -- (6) in polynomial form: `R R'² = c²A - c²R + (λ/3) R³` near `t`
  have hev : (fun s ↦ c ^ 2 * A - c ^ 2 * R s + lam / 3 * R s ^ 3) =ᶠ[𝓝 t]
      fun s ↦ R s * R' s ^ 2 := by
    filter_upwards [h6] with s ⟨hs, h⟩
    unfold eq6 at h
    field_simp at h
    linear_combination (-1 / 3 : ℝ) * h
  have hL := h1.mul (h2.pow 2)
  have hRhs := (((hasDerivAt_const t (c ^ 2 * A)).sub (h1.const_mul (c ^ 2))).add
    ((h1.pow 3).const_mul (lam / 3))).congr_of_eventuallyEq hev.symm
  have huniq := hL.unique hRhs
  simp only [Pi.pow_apply] at huniq
  push_cast at huniq
  unfold eq4
  have hfac : R' t * (R' t ^ 2 + 2 * R t * R'' + c ^ 2 - lam * R t ^ 2) = 0 := by
    linear_combination huniq
  have h0 : R' t ^ 2 + 2 * R t * R'' + c ^ 2 - lam * R t ^ 2 = 0 :=
    (mul_eq_zero.1 hfac).resolve_left hR'
  field_simp
  linear_combination h0

/-! ### Density and mass, (8) and (9) -/

/-- (5), (6) ⇒ (8): `ρ = 3A/(κR³)`. -/
theorem density_eq {κ c lam ρ A R R' : ℝ} (hκ : κ ≠ 0) (hc : c ≠ 0) (hR : R ≠ 0)
    (h5 : eq5 κ c lam ρ R R') (h6 : eq6 c lam A R R') : ρ = 3 * A / (κ * R ^ 3) := by
  unfold eq5 at h5
  unfold eq6 at h6
  field_simp at h5 h6
  have : R' ^ 2 = c ^ 2 * (A - R) / R + lam * R ^ 2 / 3 := by
    field_simp; linear_combination h6
  rw [this] at h5
  field_simp at h5
  have h7 : c ^ 2 * (κ * R ^ 3 * ρ - 3 * A) = 0 := by linear_combination (-1 : ℝ) * h5
  have h8 : κ * R ^ 3 * ρ - 3 * A = 0 := (mul_eq_zero.1 h7).resolve_left (by positivity)
  field_simp
  linear_combination h8

/-- The volume of space at radius `R`: with spatial line element
`R²(dx₁² + sin²x₁ dx₂² + sin²x₁ sin²x₂ dx₃²)` and Friedmann's ranges `x₁, x₂ ∈ (0, π)`,
`x₃ ∈ (0, 2π)` (§1.4), the volume element is `R³ sin²x₁ sin x₂`, and the volume is `2π²R³`. -/
theorem volume_of_space (R : ℝ) :
    ∫ x₁ in (0 : ℝ)..π, ∫ x₂ in (0 : ℝ)..π, ∫ _x₃ in (0 : ℝ)..(2 * π),
      R ^ 3 * sin x₁ ^ 2 * sin x₂ = 2 * π ^ 2 * R ^ 3 := by
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero,
    intervalIntegral.integral_const_mul, integral_sin, cos_zero, cos_pi]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_sin_sq]
  simp
  ring

/-- The total mass of space, `M̄ = ρ · 2π²R³` (density times the volume of `volume_of_space`). -/
noncomputable def totalMass (R ρ : ℝ) : ℝ := 2 * π ^ 2 * R ^ 3 * ρ

/-- (8) ⇒ (9): `A = κM̄/(6π²)`. -/
theorem A_eq_mass {κ A R : ℝ} (hκ : κ ≠ 0) (hR : R ≠ 0) :
    A = κ * totalMass R (3 * A / (κ * R ^ 3)) / (6 * π ^ 2) := by
  unfold totalMass
  field_simp
  ring

/-- "Ist `M̄` positiv, so wird `A` auch positiv" (for `κ > 0`). -/
theorem A_pos_iff {κ A R : ℝ} (hκ : 0 < κ) (hR : R ≠ 0) :
    0 < A ↔ 0 < totalMass R (3 * A / (κ * R ^ 3)) := by
  have h := A_eq_mass (A := A) hκ.ne' hR
  constructor
  · intro hA
    by_contra hM
    push Not at hM
    have : κ * totalMass R (3 * A / (κ * R ^ 3)) / (6 * π ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hκ.le hM) (by positivity)
    linarith
  · intro hM
    rw [h]
    positivity

/-! ### The static world (§2, no. 1): Einstein's cylinder world -/

/-- A constant radius solves (4) iff `λ = c²/R²`. -/
theorem static_eq4_iff {c lam R : ℝ} : eq4 c lam R 0 0 ↔ lam = c ^ 2 / R ^ 2 := by
  unfold eq4
  constructor <;> intro h <;> simp at * <;> linarith

/-- Einstein's density `ρ = 2/(κR²)` from (5) in the static world. -/
theorem static_density {κ c lam ρ R : ℝ} (hκ : κ ≠ 0) (hc : c ≠ 0) (hR : R ≠ 0)
    (hlam : lam = c ^ 2 / R ^ 2) (h5 : eq5 κ c lam ρ R 0) : ρ = 2 / (κ * R ^ 2) := by
  unfold eq5 at h5
  subst hlam
  field_simp at h5
  have h7 : c ^ 2 * (κ * R ^ 2 * ρ - 2) = 0 := by linear_combination (-1 : ℝ) * h5
  have h8 : κ * R ^ 2 * ρ - 2 = 0 := (mul_eq_zero.1 h7).resolve_left (by positivity)
  field_simp
  linear_combination h8

/-- Einstein's total mass `M̄ = 4π²R/κ` of the cylinder world. -/
theorem static_mass {κ R : ℝ} (hκ : κ ≠ 0) (hR : R ≠ 0) :
    totalMass R (2 / (κ * R ^ 2)) = 4 * π ^ 2 * R / κ := by
  unfold totalMass
  field_simp
  ring

/-! ### The roots of `A - x + (λ/(3c²)) x³` (§2, nos. 3–6) -/

/-- The radicand of (7): `A - x + (λ/(3c²)) x³`. -/
noncomputable def radicand (c lam A x : ℝ) : ℝ := A - x + lam / (3 * c ^ 2) * x ^ 3

/-- The family (10), `y x³ - x + A = 0`, i.e. `y = (x - A)/x³`, has its maximum
`y = 4/(27A²)` at `x = 3A/2`. -/
theorem cubic_max {A x : ℝ} (hA : 0 < A) (hx : 0 < x) : (x - A) / x ^ 3 ≤ 4 / (27 * A ^ 2) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (2 * x - 3 * A), mul_nonneg (sq_nonneg (2 * x - 3 * A))
    (by linarith : (0 : ℝ) ≤ x + 3 * A)]

/-- The maximum in (10) is attained only at `x = 3A/2`. -/
theorem cubic_max_eq_iff {A x : ℝ} (hA : 0 < A) (hx : 0 < x) :
    (x - A) / x ^ 3 = 4 / (27 * A ^ 2) ↔ x = 3 * A / 2 := by
  constructor
  · intro h
    rw [div_eq_div_iff (by positivity) (by positivity)] at h
    have hfac : (2 * x - 3 * A) ^ 2 * (x + 3 * A) = 0 := by linear_combination (-1 : ℝ) * h
    have : (2 * x - 3 * A) ^ 2 = 0 :=
      (mul_eq_zero.1 hfac).resolve_right (by linarith)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  · rintro rfl
    field_simp
    ring

/-- §2, no. 4: for `λ > λ₁ = 4c²/(9A²)` the equation `A - x + (λ/(3c²)) x³ = 0` has no
positive root; the radicand is positive for all `x > 0`. -/
theorem radicand_pos {c lam A x : ℝ} (hc : c ≠ 0) (hA : 0 < A) (hx : 0 < x)
    (hlam : 4 * c ^ 2 / (9 * A ^ 2) < lam) : 0 < radicand c lam A x := by
  unfold radicand
  have hm := cubic_max hA hx
  have hc2 : 0 < c ^ 2 := by positivity
  have hy : 4 / (27 * A ^ 2) < lam / (3 * c ^ 2) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hlam
    nlinarith
  have : (x - A) / x ^ 3 < lam / (3 * c ^ 2) := lt_of_le_of_lt hm hy
  rw [div_lt_iff₀ (by positivity)] at this
  linarith

/-- At `λ = λ₁` the radicand has the double root `x = 3A/2`. -/
theorem radicand_critical {c A : ℝ} (hc : c ≠ 0) :
    radicand c (4 * c ^ 2 / (9 * A ^ 2)) A (3 * A / 2) = 0 := by
  unfold radicand
  field_simp
  ring

/-- §2, no. 3: for negative `λ` the equation `A - x + (λ/(3c²)) x³ = 0` has a root `x₀` in
`(0, A)`. -/
theorem exists_root_of_neg {c lam A : ℝ} (hc : c ≠ 0) (hA : 0 < A) (hlam : lam < 0) :
    ∃ x₀ ∈ Ioo 0 A, radicand c lam A x₀ = 0 := by
  have hcont : ContinuousOn (radicand c lam A) (Icc 0 A) := by
    unfold radicand; fun_prop
  have h0 : radicand c lam A 0 = A := by simp [radicand]
  have hAv : radicand c lam A A < 0 := by
    unfold radicand
    have : lam / (3 * c ^ 2) < 0 := div_neg_of_neg_of_pos hlam (by positivity)
    nlinarith [pow_pos hA 3]
  have := intermediate_value_Ioo' hA.le hcont
  obtain ⟨x, hx, hx0⟩ := this ⟨hAv, by rw [h0]; exact hA⟩
  exact ⟨x, hx, hx0⟩

/-- §2, no. 4, the monotonic world of the first kind: if `λ > λ₁ = 4c²/(9A²)` and `R > 0`
satisfies (6) on a time interval, then `R` is strictly monotone there. -/
theorem monotonic_world {R R' : ℝ → ℝ} {c lam A a b : ℝ} (hc : c ≠ 0) (hA : 0 < A)
    (hlam : 4 * c ^ 2 / (9 * A ^ 2) < lam)
    (hR : ∀ s ∈ Icc a b, 0 < R s)
    (h1 : ∀ s ∈ Icc a b, HasDerivAt R (R' s) s)
    (h6 : ∀ s ∈ Icc a b, eq6 c lam A (R s) (R' s)) :
    StrictMonoOn R (Icc a b) ∨ StrictAntiOn R (Icc a b) := by
  have hne : ∀ s ∈ Icc a b, R' s ≠ 0 := by
    intro s hs h0
    have h := h6 s hs
    unfold eq6 at h
    rw [h0] at h
    have hp := radicand_pos hc hA (hR s hs) hlam
    unfold radicand at hp
    have : 0 < (A - R s + lam / (3 * c ^ 2) * R s ^ 3) / R s := div_pos hp (hR s hs)
    simp at h
    linarith
  have hcont : ContinuousOn R (Icc a b) := fun s hs ↦ (h1 s hs).continuousAt.continuousWithinAt
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (convex_Icc a b)
    (fun s hs ↦ (h1 s hs).hasDerivWithinAt) hne with hneg | hpos
  · right
    refine strictAntiOn_of_deriv_neg (convex_Icc a b) hcont fun s hs ↦ ?_
    have hs' := interior_subset hs
    rw [(h1 s hs').deriv]
    exact hneg s hs'
  · left
    refine strictMonoOn_of_deriv_pos (convex_Icc a b) hcont fun s hs ↦ ?_
    have hs' := interior_subset hs
    rw [(h1 s hs').deriv]
    exact hpos s hs'

/-! ### The periodic world for `λ = 0` (§2, no. 6): the cycloid -/

/-- `φ(η) = η - sin η`; the cycloid has `t = (A/(2c)) φ(η)`. -/
noncomputable def phi (η : ℝ) : ℝ := η - sin η

theorem phi_strictMono : StrictMono phi := by
  intro a b hab
  unfold phi
  have hd : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
  have h := abs_sin_lt_abs (x := (b - a) / 2) (by positivity)
  have hss : sin b - sin a = 2 * sin ((b - a) / 2) * cos ((b + a) / 2) := sin_sub_sin b a
  have hcos := abs_cos_le_one ((b + a) / 2)
  have : |sin b - sin a| < b - a := by
    rw [hss, abs_mul, abs_mul, abs_two]
    rw [abs_of_pos (by linarith : (0 : ℝ) < (b - a) / 2)] at h
    nlinarith [abs_nonneg (sin ((b - a) / 2)), abs_nonneg (cos ((b + a) / 2))]
  linarith [le_abs_self (sin b - sin a)]

theorem phi_continuous : Continuous phi := by unfold phi; fun_prop

theorem phi_surjective : Function.Surjective phi := by
  refine phi_continuous.surjective ?_ ?_
  · refine tendsto_atTop_mono (fun η ↦ ?_) (tendsto_atTop_add_const_right _ (-1) tendsto_id)
    simp only [id, phi]; linarith [sin_le_one η]
  · refine tendsto_atBot_mono (fun η ↦ ?_) (tendsto_atBot_add_const_right _ 1 tendsto_id)
    simp only [id, phi]; linarith [neg_one_le_sin η]

/-- `η ↦ η - sin η` as an order isomorphism of `ℝ`. -/
noncomputable def phiIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective phi phi_strictMono phi_surjective

/-- The inverse `ψ = φ⁻¹`. -/
noncomputable def psi (u : ℝ) : ℝ := phiIso.symm u

theorem phi_psi (u : ℝ) : phi (psi u) = u := phiIso.apply_symm_apply u

theorem psi_phi (η : ℝ) : psi (phi η) = η := phiIso.symm_apply_apply η

theorem psi_continuous : Continuous psi := phiIso.symm.continuous

/-- The world radius of the periodic world with `λ = 0`, as a function of time:
`R(t) = (A/2)(1 - cos η)` where `t = (A/(2c))(η - sin η)`. -/
noncomputable def periodicWorld (A c t : ℝ) : ℝ := A / 2 * (1 - cos (psi (2 * c * t / A)))

/-- For `λ = 0`, `R(t)` solves Friedmann's equation (6) at every time with `R(t) ≠ 0`. -/
theorem periodicWorld_eq6 {A c t : ℝ} (hA : A ≠ 0) (hc : c ≠ 0)
    (hR : periodicWorld A c t ≠ 0) :
    ∃ R', HasDerivAt (periodicWorld A c) R' t ∧ eq6 c 0 A (periodicWorld A c t) R' := by
  set u := 2 * c * t / A with hu
  set η := psi u with hη
  have hcos : 1 - cos η ≠ 0 := by
    intro h; apply hR; unfold periodicWorld; rw [← hu, ← hη, h, mul_zero]
  -- derivative of `ψ` at `u`
  have hphi : HasDerivAt phi (1 - cos η) η := by
    unfold phi; exact (hasDerivAt_id' η).sub (hasDerivAt_sin η)
  have hpsi : HasDerivAt psi (1 - cos η)⁻¹ u :=
    HasDerivAt.of_local_left_inverse psi_continuous.continuousAt hphi hcos
      (Eventually.of_forall phi_psi)
  have hu' : HasDerivAt (fun t ↦ 2 * c * t / A) (2 * c / A) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * c)).div_const A
  have hcomp := hpsi.comp t hu'
  have hR' := ((hcomp.cos).const_sub 1).const_mul (A / 2)
  refine ⟨_, hR', ?_⟩
  unfold eq6 periodicWorld
  simp only [Function.comp_apply, ← hu, ← hη]
  have hs : sin η ^ 2 = (1 - cos η) * (1 + cos η) := by nlinarith [sin_sq_add_cos_sq η]
  field_simp
  rw [hs]
  ring

theorem periodicWorld_zero (A c : ℝ) : periodicWorld A c 0 = 0 := by
  have : psi 0 = 0 := by simpa [phi] using psi_phi 0
  simp [periodicWorld, this]

/-- The radius returns to zero at `t = πA/c`, Friedmann's period (15) (exact for `λ = 0`). -/
theorem periodicWorld_period {A c : ℝ} (hA : A ≠ 0) (hc : c ≠ 0) :
    periodicWorld A c (π * A / c) = 0 := by
  have h1 : 2 * c * (π * A / c) / A = phi (2 * π) := by
    simp [phi]; field_simp
  simp [periodicWorld, h1, psi_phi]

/-- At half the period, `t = πA/(2c)`, the radius reaches its maximum `A`. -/
theorem periodicWorld_half {A c : ℝ} (hA : A ≠ 0) (hc : c ≠ 0) :
    periodicWorld A c (π * A / (2 * c)) = A := by
  have h1 : 2 * c * (π * A / (2 * c)) / A = phi π := by
    simp [phi]; field_simp
  simp [periodicWorld, h1, psi_phi]
  ring

/-- `R` is periodic with period `t_π = πA/c`. -/
theorem periodicWorld_periodic {A c : ℝ} (hA : A ≠ 0) (hc : c ≠ 0) (t : ℝ) :
    periodicWorld A c (t + π * A / c) = periodicWorld A c t := by
  have hshift : ∀ u, psi (u + 2 * π) = psi u + 2 * π := by
    intro u
    have : u + 2 * π = phi (psi u + 2 * π) := by
      simp only [phi]; rw [sin_add_two_pi]; have := phi_psi u; unfold phi at this; linarith
    rw [this, psi_phi]
  have h1 : 2 * c * (t + π * A / c) / A = 2 * c * t / A + 2 * π := by
    field_simp
  simp only [periodicWorld, h1, hshift, cos_add_two_pi]

/-- The radius stays between `0` and `A` (here `x₀ = A`). -/
theorem periodicWorld_le {A : ℝ} (hA : 0 ≤ A) (c t : ℝ) :
    0 ≤ periodicWorld A c t ∧ periodicWorld A c t ≤ A := by
  unfold periodicWorld
  have h1 := cos_le_one (psi (2 * c * t / A))
  have h2 := neg_one_le_cos (psi (2 * c * t / A))
  constructor <;> nlinarith

end SovietLean.Friedmann1922
