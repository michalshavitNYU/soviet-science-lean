module

public import SovietLean.HighEnergy.Friedmann1922
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Friedmann (1924), *Über die Möglichkeit einer Welt mit konstanter negativer Krümmung des Raumes*

Entry: `entries/high-energy/1924-friedmann-negative-kruemmung/`.
Companion of `SovietLean.HighEnergy.Friedmann1922` (entry `1922-friedmann-kruemmung-des-raumes`).

**Setting.** Friedmann keeps the field equations (A), (B), (C) of his 1922 note and replaces the
spherical space by a space of constant *negative* curvature `-1/R²`, written in the half-space
(Poincaré) form

  `ds² = R²(dx₁² + dx₂² + dx₃²)/x₃² + M² dx₄²`                    (D′)
  `dτ² = -(R²/c²)(dx₁² + dx₂² + dx₃²)/x₃² + M² dx₄²`              (D″)

with `R = R(x₄)` and `M` a function of all four coordinates. (D′) is a definite form, (D″) the
indefinite one obtained "by a change of notation".

* **§2, nos. 1–2: stationary worlds** (`R' = 0`). In the form (D′) the equations (A) with
  `i, k = 1, 2, 3` give the system (2) for `M`; with `M = (P + Q)/x₃ + L` (1) and (3) Friedmann
  obtains (4), from which `λR² = 3` [printed `λR³ = 3`, (5)] when `M` depends on `x₁` or `x₂`,
  and then the single equation

    `∂L/∂x₃ + L/x₃ = 2n`                                       (6)

  whose solutions are `L = L₀(x₄)/x₃ + x₃` for `n = 1` (7) and `L = L₀(x₄)/x₃` for `n = 0` (8).
  In both cases the density is zero, (D′₁), (D′₂). If `M` depends only on `x₃, x₄` there are two
  cases, `λR² = 3, M = M₀(x₄)/x₃` (density zero) and `λR² = 1, M = M(x₄)`. In the second, after
  passing to (D″) with `M = 1`,

    `λ = -c²/R²`,   `ρ = -2/(κR²)`                               (D″₃)

  so the density is negative. *Conclusion:* a stationary world of constant negative spatial
  curvature has zero or negative density.

* **§2, no. 3: non-stationary worlds.** With `M = 1`, in the form (D′) the equations reduce to

    `R'²/R² + 2RR''/R² + 1/R² - λ = 0`,                         (9)

  which is (4) of the 1922 note with `c = 1`. In the form (D″) the equation (unnumbered) is

    `R'²/R² + 2RR''/R² - c²/R² - λ = 0`,

  whose integral (unnumbered) is

    `R'²/c² = (A + R + (λ/(3c²)) R³)/R`,   `A` an arbitrary constant,

  and the density is

    `ρ = 3A/(κR³)`.                                              (10)

  So for `A > 0` the density is positive: non-stationary worlds of constant negative curvature
  with positive density exist.

**What is not formalized.** Mathlib has no Lorentzian geometry, so the passage from Einstein's
equations (A)–(C) and the metrics (D′), (D″) to the equations above is not formalized. We take the
ordinary differential equations as Friedmann prints them, as relations between numbers `R, R', R''`
at one time, and prove what follows. The partial differential system (2) and the step from (4) to
(5) are not formalized; only the ordinary differential equation (6) for `L` is.

Friedmann does not print the `i = k = 4` equation that he uses to compute `ρ` in the
non-stationary case. We use its form for (D″) with `M = 1`,

  `3R'²/R² - 3c²/R² - λ = κc²ρ`                                  (`eq44`, not printed)

which is (5) of the 1922 note with `c²` replaced by `-c²` (the curvature `+1/R²` replaced by
`-1/R²`). It is an explicit hypothesis of every theorem that uses it. With it, both densities that
Friedmann does print, `ρ = -2/(κR²)` in (D″₃) and `ρ = 3A/(κR³)` in (10), are recovered.

Lean reserves the letter `λ`, so the cosmological constant is called `lam`; `κ` is Einstein's
constant. Nothing is rescaled.

## Formal version

| Paper | Lean | Status |
|---|---|---|
| (6): `L = L₀/x₃ + n x₃` solves `∂L/∂x₃ + L/x₃ = 2n` | `eq6_solution` | proved |
| (6): every solution on `x₃ > 0` has this form | `eq6_general` | proved |
| (6) ⇒ (7), (8): the cases `n = 1`, `n = 0` | `eq7_of_eq6`, `eq8_of_eq6` | proved |
| (9) is (4) of the 1922 note with `c = 1` | `eq9_iff_eq4` | proved |
| §2.3: `RR'² - c²R - (λ/3)R³` is constant along (D″) | `energy_hasDerivAt` | proved |
| §2.3: the first integral `R'²/c² = (A + R + (λ/(3c²))R³)/R` | `eqA_of_eqR` | proved |
| §2.3: converse where `R' ≠ 0` | `eqR_of_eqA` | proved |
| (10): `ρ = 3A/(κR³)` | `density_eq` | proved |
| (10): `ρ > 0` iff `A > 0` | `density_pos_iff` | proved |
| (D″₃): constant `R` solves the (D″) equation iff `λ = -c²/R²` | `static_iff` | proved |
| (D″₃): then `ρ = -2/(κR²)` | `static_density` | proved |
| §2.2: no static (D″) world with `ρ ≥ 0` | `static_density_neg` | proved |
| for `λ ≥ 0, A ≥ 0`: the radicand has no positive root | `radicand_pos` | proved |
| ... so the world is monotonic | `monotonic_world` | proved |
| for `λ < 0, A > 0`: a positive root `x₀` exists | `exists_root_of_neg` | proved |
| ... and `R` is bounded | `bounded_of_neg` | proved |
| `λ = 0`: the hyperbolic cycloid solves the first integral | `openWorld_eqA` | proved |
| ... `R = (A/2)(cosh η - 1)` at `t = (A/(2c))(sinh η - η)` | `openWorld_param` | proved |
| ... `R(0) = 0` | `openWorld_zero` | proved |
| ... `R` strictly increasing for `t ≥ 0` | `openWorld_strictMonoOn` | proved |
| ... `R → ∞` as `t → ∞` | `openWorld_tendsto` | proved |

Notes on matching the source.

* The classification for `λ ≥ 0` and `λ < 0` and the explicit `λ = 0` solution are **not printed**
  in the 1924 note: Friedmann only says that "the whole discussion" of the 1922 equation (4)
  carries over to (9). For the (D″) form the radicand is `A + x + (λ/(3c²))x³` instead of
  `A - x + (λ/(3c²))x³`, and these theorems record what the transfer gives.
* For `λ = 0` the first integral is solved by `R = (A/2)(cosh η - 1)`, `t = (A/(2c))(sinh η - η)`,
  the hyperbolic analogue of the cycloid of `Friedmann1922.periodicWorld`. We define `R(t)` by
  inverting `η ↦ sinh η - η` (strictly increasing by Mathlib's `Real.sinh_sub_id_strictMono`).
* Hypotheses `R ≠ 0`, `c ≠ 0`, `κ ≠ 0` are explicit where the paper divides by these quantities.
-/

@[expose] public section

open Real Set Filter
open scoped Topology

namespace SovietLean.Friedmann1924

/-! ### The stationary world: the equation (6) for `L` and its solutions (7), (8) -/

/-- Eq. (6): `∂L/∂x₃ + L/x₃ = 2n`, at the point `x₃ = x`, with `L' = ∂L/∂x₃`. -/
def eq6 (n x L L' : ℝ) : Prop := L' + L / x = 2 * n

/-- `L = L₀/x₃ + n x₃` solves (6) at every `x₃ ≠ 0`. For `n = 1` this is (7), for `n = 0` (8). -/
theorem eq6_solution (n L₀ : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y ↦ L₀ / y + n * y) (-L₀ / x ^ 2 + n) x ∧
      eq6 n x (L₀ / x + n * x) (-L₀ / x ^ 2 + n) := by
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun y ↦ L₀ / y) (-L₀ / x ^ 2) x := by
      have := (hasDerivAt_inv hx).const_mul L₀
      convert this using 1
      · ext y; simp [div_eq_mul_inv]
      · field_simp
    convert h1.add ((hasDerivAt_id' x).const_mul n) using 1
    ring
  · unfold eq6
    field_simp
    ring

/-- Every solution of (6) on the half-space `x₃ > 0` is `L = L₀/x₃ + n x₃` for a constant `L₀`
(constant in `x₃`; in the paper `L₀` depends on `x₄`). -/
theorem eq6_general {n : ℝ} {L L' : ℝ → ℝ}
    (hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt L (L' x) x)
    (h6 : ∀ x ∈ Ioi (0 : ℝ), eq6 n x (L x) (L' x)) :
    ∃ L₀, ∀ x ∈ Ioi (0 : ℝ), L x = L₀ / x + n * x := by
  -- `x L - n x²` has derivative `x (L' + L/x - 2n) = 0`
  have hg : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y ↦ y * L y - n * y ^ 2) 0 x := by
    intro x hx
    have h := ((hasDerivAt_id' x).mul (hd x hx)).sub ((hasDerivAt_pow 2 x).const_mul n)
    convert h using 1
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h6x := h6 x hx
    unfold eq6 at h6x
    field_simp at h6x
    push_cast
    linear_combination (-1 : ℝ) * h6x
  obtain ⟨a, ha⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun x hx ↦ (hg x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hg x hx).deriv)
  refine ⟨a, fun x hx ↦ ?_⟩
  have h := ha x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp
  linear_combination h

/-- (6) ⇒ (7): for `n = 1`, `L = L₀/x₃ + x₃`. -/
theorem eq7_of_eq6 {L L' : ℝ → ℝ}
    (hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt L (L' x) x)
    (h6 : ∀ x ∈ Ioi (0 : ℝ), eq6 1 x (L x) (L' x)) :
    ∃ L₀, ∀ x ∈ Ioi (0 : ℝ), L x = L₀ / x + x := by
  simpa using eq6_general hd h6

/-- (6) ⇒ (8): for `n = 0`, `L = L₀/x₃`. -/
theorem eq8_of_eq6 {L L' : ℝ → ℝ}
    (hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt L (L' x) x)
    (h6 : ∀ x ∈ Ioi (0 : ℝ), eq6 0 x (L x) (L' x)) :
    ∃ L₀, ∀ x ∈ Ioi (0 : ℝ), L x = L₀ / x := by
  simpa using eq6_general hd h6

/-! ### The non-stationary world: equation (9) and its form for (D″) -/

/-- Eq. (9), in the form (D′): `R'²/R² + 2RR''/R² + 1/R² - λ = 0`. -/
def eq9 (lam R R' R'' : ℝ) : Prop :=
  R' ^ 2 / R ^ 2 + 2 * R * R'' / R ^ 2 + 1 / R ^ 2 - lam = 0

/-- "die letztere geht genau in Gl. (9) über, wenn man dort `c = 1` setzt": (9) is the 1922
equation (4) with `c = 1`. -/
theorem eq9_iff_eq4 {lam R R' R'' : ℝ} :
    eq9 lam R R' R'' ↔ SovietLean.Friedmann1922.eq4 1 lam R R' R'' := by
  unfold eq9 SovietLean.Friedmann1922.eq4
  norm_num

/-- §2, no. 3, the equation for `R` in the form (D″) (unnumbered):
`R'²/R² + 2RR''/R² - c²/R² - λ = 0`. -/
def eqR (c lam R R' R'' : ℝ) : Prop :=
  R' ^ 2 / R ^ 2 + 2 * R * R'' / R ^ 2 - c ^ 2 / R ^ 2 - lam = 0

/-- §2, no. 3, its integral (unnumbered): `R'²/c² = (A + R + (λ/(3c²)) R³)/R`. -/
def eqA (c lam A R R' : ℝ) : Prop :=
  R' ^ 2 / c ^ 2 = (A + R + lam / (3 * c ^ 2) * R ^ 3) / R

/-- The equation (A) with `i = k = 4` for (D″) with `M = 1`, which Friedmann uses but does not
print: `3R'²/R² - 3c²/R² - λ = κc²ρ`. (The 1922 equation (5) with `c²` replaced by `-c²`.) -/
def eq44 (κ c lam ρ R R' : ℝ) : Prop :=
  3 * R' ^ 2 / R ^ 2 - 3 * c ^ 2 / R ^ 2 - lam = κ * c ^ 2 * ρ

/-- The quantity `R R'² - c² R - (λ/3) R³`, which the (D″) equation keeps constant; it equals
`c² A`. (In 1922 the middle sign was `+`.) -/
noncomputable def energy (c lam : ℝ) (R R' : ℝ → ℝ) (s : ℝ) : ℝ :=
  R s * R' s ^ 2 - c ^ 2 * R s - lam / 3 * R s ^ 3

/-- Along a solution of the (D″) equation, `R R'² - c²R - (λ/3)R³` has derivative zero. -/
theorem energy_hasDerivAt {R R' : ℝ → ℝ} {R'' c lam t : ℝ}
    (h1 : HasDerivAt R (R' t) t) (h2 : HasDerivAt R' R'' t) (hR : R t ≠ 0)
    (hE : eqR c lam (R t) (R' t) R'') :
    HasDerivAt (energy c lam R R') 0 t := by
  have h := ((h1.mul (h2.pow 2)).sub (h1.const_mul (c ^ 2))).sub ((h1.pow 3).const_mul (lam / 3))
  unfold energy
  convert h using 1
  unfold eqR at hE
  field_simp at hE
  simp only [Pi.pow_apply]
  push_cast
  linear_combination (-(R' t)) * hE

/-- "Die Integration dieser Gleichung liefert uns die Beziehung": on a time interval where
`R ≠ 0`, every solution of the (D″) equation satisfies `R'²/c² = (A + R + (λ/(3c²))R³)/R`, with
the constant `A = (R R'² - c²R - (λ/3)R³)/c²`. -/
theorem eqA_of_eqR {R R' R'' : ℝ → ℝ} {c lam a b : ℝ} (hc : c ≠ 0)
    (hR : ∀ s ∈ Icc a b, R s ≠ 0)
    (h1 : ∀ s ∈ Icc a b, HasDerivAt R (R' s) s)
    (h2 : ∀ s ∈ Icc a b, HasDerivAt R' (R'' s) s)
    (hE : ∀ s ∈ Icc a b, eqR c lam (R s) (R' s) (R'' s)) :
    ∀ s ∈ Icc a b, eqA c lam (energy c lam R R' a / c ^ 2) (R s) (R' s) := by
  have hd : ∀ s ∈ Icc a b, HasDerivAt (energy c lam R R') 0 s := fun s hs ↦
    energy_hasDerivAt (h1 s hs) (h2 s hs) (hR s hs) (hE s hs)
  have hconst := constant_of_has_deriv_right_zero
    (fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs ↦ (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
  intro s hs
  have hEs := hconst s hs
  have hRs := hR s hs
  unfold eqA
  rw [← hEs]
  unfold energy
  field_simp
  ring

/-- The converse where `R' ≠ 0`: differentiating the integral gives back the (D″) equation. -/
theorem eqR_of_eqA {R R' : ℝ → ℝ} {R'' c lam A t : ℝ} (hc : c ≠ 0) (hR' : R' t ≠ 0)
    (h1 : HasDerivAt R (R' t) t) (h2 : HasDerivAt R' R'' t)
    (hA : ∀ᶠ s in 𝓝 t, R s ≠ 0 ∧ eqA c lam A (R s) (R' s)) :
    eqR c lam (R t) (R' t) R'' := by
  have hRt : R t ≠ 0 := hA.self_of_nhds.1
  have hev : (fun s ↦ c ^ 2 * A + c ^ 2 * R s + lam / 3 * R s ^ 3) =ᶠ[𝓝 t]
      fun s ↦ R s * R' s ^ 2 := by
    filter_upwards [hA] with s ⟨hs, h⟩
    unfold eqA at h
    field_simp at h
    linear_combination (-1 / 3 : ℝ) * h
  have hL := h1.mul (h2.pow 2)
  have hRhs := (((hasDerivAt_const t (c ^ 2 * A)).add (h1.const_mul (c ^ 2))).add
    ((h1.pow 3).const_mul (lam / 3))).congr_of_eventuallyEq hev.symm
  have huniq := hL.unique hRhs
  simp only [Pi.pow_apply] at huniq
  push_cast at huniq
  unfold eqR
  have hfac : R' t * (R' t ^ 2 + 2 * R t * R'' - c ^ 2 - lam * R t ^ 2) = 0 := by
    linear_combination huniq
  have h0 : R' t ^ 2 + 2 * R t * R'' - c ^ 2 - lam * R t ^ 2 = 0 :=
    (mul_eq_zero.1 hfac).resolve_left hR'
  field_simp
  linear_combination h0

/-! ### The density (10) -/

/-- (10): with the integral and the `(4,4)` equation, `ρ = 3A/(κR³)`. -/
theorem density_eq {κ c lam ρ A R R' : ℝ} (hκ : κ ≠ 0) (hc : c ≠ 0) (hR : R ≠ 0)
    (h44 : eq44 κ c lam ρ R R') (hA : eqA c lam A R R') : ρ = 3 * A / (κ * R ^ 3) := by
  unfold eq44 at h44
  unfold eqA at hA
  field_simp at h44 hA
  have : R' ^ 2 = c ^ 2 * (A + R) / R + lam * R ^ 2 / 3 := by
    field_simp; linear_combination hA
  rw [this] at h44
  field_simp at h44
  have h7 : c ^ 2 * (κ * R ^ 3 * ρ - 3 * A) = 0 := by linear_combination (-1 : ℝ) * h44
  have h8 : κ * R ^ 3 * ρ - 3 * A = 0 := (mul_eq_zero.1 h7).resolve_left (by positivity)
  field_simp
  linear_combination h8

/-- "Die Formel (10) zeigt, daß für ein positives `A` die Dichte der Materie ebenfalls positiv
ist" (for `κ > 0`, `R > 0`; and conversely). -/
theorem density_pos_iff {κ A R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    0 < 3 * A / (κ * R ^ 3) ↔ 0 < A := by
  have h : 0 < κ * R ^ 3 := by positivity
  rw [div_pos_iff_of_pos_right h]
  constructor <;> intro h' <;> linarith

/-! ### The stationary world in the form (D″) -/

/-- A constant radius solves the (D″) equation iff `λ = -c²/R²`, as in (D″₃). -/
theorem static_iff {c lam R : ℝ} : eqR c lam R 0 0 ↔ lam = -c ^ 2 / R ^ 2 := by
  unfold eqR
  constructor <;> intro h
  · simp at h; rw [neg_div]; linarith
  · simp [h, neg_div]

/-- (D″₃): the density of the static world is `ρ = -2/(κR²)`. -/
theorem static_density {κ c lam ρ R : ℝ} (hκ : κ ≠ 0) (hc : c ≠ 0) (hR : R ≠ 0)
    (hlam : lam = -c ^ 2 / R ^ 2) (h44 : eq44 κ c lam ρ R 0) : ρ = -2 / (κ * R ^ 2) := by
  unfold eq44 at h44
  subst hlam
  field_simp at h44
  have h7 : c ^ 2 * (κ * R ^ 2 * ρ + 2) = 0 := by linear_combination (-1 : ℝ) * h44
  have h8 : κ * R ^ 2 * ρ + 2 = 0 := (mul_eq_zero.1 h7).resolve_left (by positivity)
  field_simp
  linear_combination h8

/-- "Dieser Fall ergibt also für `ρ` einen negativen Wert": every static solution of the (D″)
equations has negative density (for `κ > 0`). -/
theorem static_density_neg {κ c lam ρ R : ℝ} (hκ : 0 < κ) (hc : c ≠ 0) (hR : R ≠ 0)
    (hE : eqR c lam R 0 0) (h44 : eq44 κ c lam ρ R 0) : ρ < 0 := by
  rw [static_density hκ.ne' hc hR (static_iff.1 hE) h44]
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

/-! ### The non-stationary worlds by the sign of `λ` -/

/-- The radicand of the integral: `A + x + (λ/(3c²)) x³` (in 1922: `A - x + ...`). -/
noncomputable def radicand (c lam A x : ℝ) : ℝ := A + x + lam / (3 * c ^ 2) * x ^ 3

/-- For `λ ≥ 0` and `A ≥ 0` the radicand is positive for every `x > 0`. -/
theorem radicand_pos {c lam A x : ℝ} (hlam : 0 ≤ lam) (hA : 0 ≤ A) (hx : 0 < x) :
    0 < radicand c lam A x := by
  unfold radicand
  have : 0 ≤ lam / (3 * c ^ 2) * x ^ 3 := by positivity
  linarith

/-- For `λ ≥ 0` and `A ≥ 0` (non-negative density), a positive solution of the integral on a
time interval is strictly monotone there: the world is monotonic. -/
theorem monotonic_world {R R' : ℝ → ℝ} {c lam A a b : ℝ} (hlam : 0 ≤ lam)
    (hA : 0 ≤ A)
    (hR : ∀ s ∈ Icc a b, 0 < R s)
    (h1 : ∀ s ∈ Icc a b, HasDerivAt R (R' s) s)
    (hE : ∀ s ∈ Icc a b, eqA c lam A (R s) (R' s)) :
    StrictMonoOn R (Icc a b) ∨ StrictAntiOn R (Icc a b) := by
  have hne : ∀ s ∈ Icc a b, R' s ≠ 0 := by
    intro s hs h0
    have h := hE s hs
    unfold eqA at h
    rw [h0] at h
    have hp := radicand_pos (c := c) hlam hA (hR s hs)
    unfold radicand at hp
    have : 0 < (A + R s + lam / (3 * c ^ 2) * R s ^ 3) / R s := div_pos hp (hR s hs)
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

/-- The key estimate for `λ < 0`: with `m = -λ/(3c²) > 0`, the radicand is negative for every
`x > 1 + (A + 2)/m`. -/
theorem radicand_neg_of_large {c lam A x : ℝ} (hc : c ≠ 0) (hlam : lam < 0) (hA : 0 ≤ A)
    (hx : 1 + (A + 2) / (-lam / (3 * c ^ 2)) < x) : radicand c lam A x < 0 := by
  unfold radicand
  set m := -lam / (3 * c ^ 2) with hm
  have hm0 : 0 < m := div_pos (by linarith) (by positivity)
  have hk : lam / (3 * c ^ 2) = -m := by rw [hm, neg_div, neg_neg]
  rw [hk]
  have hq : 0 < (A + 2) / m := by positivity
  have hx1 : 1 < x := by linarith
  have hmx : A + 2 < m * x := by
    have : (A + 2) / m < x := by linarith
    rwa [div_lt_iff₀ hm0, mul_comm] at this
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have h3 : (A + 2) * x ^ 2 < m * x ^ 3 := by
    have : (A + 2) * x ^ 2 < m * x * x ^ 2 := mul_lt_mul_of_pos_right hmx (by positivity)
    linarith [show m * x * x ^ 2 = m * x ^ 3 by ring]
  nlinarith

/-- For `λ < 0` and `A > 0` the radicand has a root `x₀ > 0`. -/
theorem exists_root_of_neg {c lam A : ℝ} (hc : c ≠ 0) (hlam : lam < 0) (hA : 0 < A) :
    ∃ x₀, 0 < x₀ ∧ radicand c lam A x₀ = 0 := by
  set X := 1 + (A + 2) / (-lam / (3 * c ^ 2)) + 1 with hX
  have hm0 : 0 < -lam / (3 * c ^ 2) := div_pos (by linarith) (by positivity)
  have hX0 : 0 < X := by have : 0 < (A + 2) / (-lam / (3 * c ^ 2)) := by positivity
                         linarith
  have hneg : radicand c lam A X < 0 := radicand_neg_of_large hc hlam hA.le (by linarith)
  have hcont : ContinuousOn (radicand c lam A) (Icc 0 X) := by
    unfold radicand; fun_prop
  have h0 : radicand c lam A 0 = A := by simp [radicand]
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo' hX0.le hcont ⟨hneg, by rw [h0]; exact hA⟩
  exact ⟨x, hx.1, hx0⟩

/-- For `λ < 0` and `A ≥ 0`, every positive solution of the integral is bounded:
`R ≤ 1 + (A + 2)/m` with `m = -λ/(3c²)`. -/
theorem bounded_of_neg {c lam A R R' : ℝ} (hc : c ≠ 0) (hlam : lam < 0) (hA : 0 ≤ A)
    (hR : 0 < R) (hE : eqA c lam A R R') : R ≤ 1 + (A + 2) / (-lam / (3 * c ^ 2)) := by
  by_contra h
  push Not at h
  have hneg := radicand_neg_of_large hc hlam hA h
  unfold eqA at hE
  unfold radicand at hneg
  have hl : 0 ≤ R' ^ 2 / c ^ 2 := by positivity
  have : (A + R + lam / (3 * c ^ 2) * R ^ 3) / R < 0 := div_neg_of_neg_of_pos hneg hR
  linarith

/-! ### The open world for `λ = 0`: the hyperbolic cycloid -/

/-- `φ(η) = sinh η - η`; the solution has `t = (A/(2c)) φ(η)`. -/
noncomputable def phi (η : ℝ) : ℝ := sinh η - η

theorem phi_strictMono : StrictMono phi := Real.sinh_sub_id_strictMono

theorem phi_continuous : Continuous phi := by unfold phi; fun_prop

theorem phi_neg (η : ℝ) : phi (-η) = -phi η := by unfold phi; rw [sinh_neg]; ring

/-- `sinh η - η ≥ η - 3` for `η ≥ 0`. -/
theorem phi_ge {η : ℝ} (hη : 0 ≤ η) : η - 3 ≤ phi η := by
  unfold phi
  rw [sinh_eq]
  have h1 := quadratic_le_exp_of_nonneg hη
  have h2 : exp (-η) ≤ 1 := exp_le_one_iff.2 (by linarith)
  nlinarith [sq_nonneg (η - 3)]

theorem phi_tendsto_atTop : Tendsto phi atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right _ (-3) tendsto_id)
  filter_upwards [eventually_ge_atTop 0] with η hη
  simpa [sub_eq_add_neg] using phi_ge hη

theorem phi_tendsto_atBot : Tendsto phi atBot atBot := by
  have h : phi = fun η ↦ -phi (-η) := by ext η; rw [phi_neg, neg_neg]
  rw [h]
  exact tendsto_neg_atTop_atBot.comp (phi_tendsto_atTop.comp tendsto_neg_atBot_atTop)

theorem phi_surjective : Function.Surjective phi :=
  phi_continuous.surjective phi_tendsto_atTop phi_tendsto_atBot

/-- `η ↦ sinh η - η` as an order isomorphism of `ℝ`. -/
noncomputable def phiIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective phi phi_strictMono phi_surjective

/-- The inverse `ψ = φ⁻¹`. -/
noncomputable def psi (u : ℝ) : ℝ := phiIso.symm u

theorem phi_psi (u : ℝ) : phi (psi u) = u := phiIso.apply_symm_apply u

theorem psi_phi (η : ℝ) : psi (phi η) = η := phiIso.symm_apply_apply η

theorem psi_continuous : Continuous psi := phiIso.symm.continuous

theorem psi_strictMono : StrictMono psi := phiIso.symm.strictMono

theorem psi_zero : psi 0 = 0 := by simpa [phi] using psi_phi 0

theorem psi_eq_zero_iff {u : ℝ} : psi u = 0 ↔ u = 0 := by
  constructor
  · intro h; rw [← phi_psi u, h]; simp [phi]
  · rintro rfl; exact psi_zero

/-- The world radius of the open world with `λ = 0`, as a function of time:
`R(t) = (A/2)(cosh η - 1)` where `t = (A/(2c))(sinh η - η)`. -/
noncomputable def openWorld (A c t : ℝ) : ℝ := A / 2 * (cosh (psi (2 * c * t / A)) - 1)

/-- The parametric form: at `t = (A/(2c))(sinh η - η)`, `R = (A/2)(cosh η - 1)`. -/
theorem openWorld_param {A c : ℝ} (hA : A ≠ 0) (hc : c ≠ 0) (η : ℝ) :
    openWorld A c (A / (2 * c) * (sinh η - η)) = A / 2 * (cosh η - 1) := by
  have h : 2 * c * (A / (2 * c) * (sinh η - η)) / A = phi η := by
    unfold phi; field_simp
  rw [openWorld, h, psi_phi]

theorem openWorld_zero (A c : ℝ) : openWorld A c 0 = 0 := by
  simp [openWorld, psi_zero]

/-- `R(t) ≠ 0` for `t ≠ 0`. -/
theorem openWorld_ne_zero {A c t : ℝ} (hA : A ≠ 0) (hc : c ≠ 0) (ht : t ≠ 0) :
    openWorld A c t ≠ 0 := by
  unfold openWorld
  have hu : 2 * c * t / A ≠ 0 := by positivity
  have hη : psi (2 * c * t / A) ≠ 0 := fun h ↦ hu (psi_eq_zero_iff.1 h)
  have := one_lt_cosh.2 hη
  have : cosh (psi (2 * c * t / A)) - 1 ≠ 0 := by linarith
  exact mul_ne_zero (div_ne_zero hA two_ne_zero) this

/-- For `λ = 0`, `R(t)` solves the first integral `R'²/c² = (A + R)/R` at every `t ≠ 0`. -/
theorem openWorld_eqA {A c t : ℝ} (hA : A ≠ 0) (hc : c ≠ 0) (ht : t ≠ 0) :
    ∃ R', HasDerivAt (openWorld A c) R' t ∧ eqA c 0 A (openWorld A c t) R' := by
  have hR := openWorld_ne_zero hA hc ht
  set u := 2 * c * t / A with hu
  set η := psi u with hη
  have hcosh : cosh η - 1 ≠ 0 := by
    intro h; apply hR; unfold openWorld; rw [← hu, ← hη, h, mul_zero]
  have hphi : HasDerivAt phi (cosh η - 1) η := by
    unfold phi; exact (hasDerivAt_sinh η).sub (hasDerivAt_id' η)
  have hpsi : HasDerivAt psi (cosh η - 1)⁻¹ u :=
    HasDerivAt.of_local_left_inverse psi_continuous.continuousAt hphi hcosh
      (Eventually.of_forall phi_psi)
  have hu' : HasDerivAt (fun t ↦ 2 * c * t / A) (2 * c / A) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * c)).div_const A
  have hcomp := hpsi.comp t hu'
  have hR' := ((hcomp.cosh).sub_const 1).const_mul (A / 2)
  refine ⟨_, hR', ?_⟩
  unfold eqA openWorld
  simp only [Function.comp_apply, ← hu, ← hη]
  have hs : sinh η ^ 2 = (cosh η - 1) * (cosh η + 1) := by rw [sinh_sq]; ring
  have hc1 : cosh η + 1 ≠ 0 := by linarith [one_le_cosh η]
  field_simp
  rw [hs]
  ring

/-- For `A > 0`, `c > 0` the radius grows strictly for `t ≥ 0`. -/
theorem openWorld_strictMonoOn {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    StrictMonoOn (openWorld A c) (Ici 0) := by
  intro s hs t ht hst
  simp only [mem_Ici] at hs ht
  unfold openWorld
  have hu : 2 * c * s / A < 2 * c * t / A := by
    apply div_lt_div_of_pos_right _ hA
    exact mul_lt_mul_of_pos_left hst (by positivity)
  have hη := psi_strictMono hu
  have hs0 : 0 ≤ psi (2 * c * s / A) := by
    rw [← psi_zero]; exact psi_strictMono.monotone (by positivity)
  have hcosh := cosh_strictMonoOn (mem_Ici.2 hs0) (mem_Ici.2 (hs0.trans hη.le)) hη
  have : 0 < A / 2 := by positivity
  nlinarith

/-- For `A > 0`, `c > 0` the radius tends to infinity: the world expands without bound. -/
theorem openWorld_tendsto {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    Tendsto (openWorld A c) atTop atTop := by
  have hu : Tendsto (fun t ↦ 2 * c * t / A) atTop atTop := by
    have : (fun t ↦ 2 * c * t / A) = fun t ↦ (2 * c / A) * t := by ext t; ring
    rw [this]
    exact tendsto_id.const_mul_atTop (by positivity)
  have hpsi : Tendsto (fun t ↦ psi (2 * c * t / A)) atTop atTop :=
    (phiIso.symm.tendsto_atTop).comp hu
  have hcosh : Tendsto cosh atTop atTop := by
    refine tendsto_atTop_mono (fun x ↦ ?_)
      (tendsto_exp_atTop.atTop_div_const (by norm_num : (0:ℝ) < 2))
    rw [cosh_eq]
    have := (exp_pos (-x)).le
    linarith
  have h := (tendsto_atTop_add_const_right _ (-1) (hcosh.comp hpsi)).const_mul_atTop
    (by positivity : (0:ℝ) < A / 2)
  refine h.congr (fun t ↦ ?_)
  simp [openWorld, sub_eq_add_neg]

end SovietLean.Friedmann1924
