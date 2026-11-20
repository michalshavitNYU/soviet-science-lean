module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Kolmogorov, Petrovsky, Piskunov (1937), *Étude de l'équation de la diffusion avec croissance
de la quantité de matière et son application à un problème biologique*

Entry: `entries/analysis/1937-kolmogorov-petrovsky-piskunov/`.

**The question.** A density `u(x, t) ∈ [0, 1]` (the concentration of an advantageous gene, in
the paper's biological application) diffuses and grows according to

  `∂u/∂t = D ∂²u/∂x² + F(u)`,  `F(0) = F(1) = 0`,  `F'(0) = α > 0`.

Started from a step (`u = 1` on one side, `0` on the other), the solution develops into a front
that moves with an asymptotic speed. The paper's answer is that this speed is
`2√(αD)`, the smallest speed for which a travelling front exists.

**What is formalized.** The elementary calculations at the heart of that answer. All of them
are proved; nothing here uses `sorry`.

* `linear_exp_solves_iff`: ahead of the front, `u` is small and the equation is close to its
  linearization `u_t = D u_xx + α u`. An exponential profile `e^{-μ(x - ct)}`, `μ > 0`, solves
  the linearization (at a point, hence everywhere) iff `c = Dμ + α/μ`.
* `two_sqrt_le_speed`, `speed_at_optimum`, `minSpeed_isLeast`: for `α, D > 0` the dispersion
  relation `c(μ) = Dμ + α/μ` is at least `2√(αD)` on `μ > 0`, with equality at `μ = √(α/D)`.
  So `2√(αD)` is the least speed of a decaying exponential solution of the linearization.
* `no_slow_exponential`: hence no such solution travels at a speed `c < 2√(αD)`.
* `travelling_wave_iff`: a travelling wave `u(x, t) = U(x - ct)` with `U` differentiable
  solves the nonlinear equation at `(x, t)` iff `D U'' + c U' + F(U) = 0` at `ξ = x - ct`.
* `exp_profile_iff`, `exists_real_rate_iff`: an exponential tail `U = e^{-μξ}` solves the
  linearized profile equation `D U'' + c U' + α U = 0` iff `Dμ² - cμ + α = 0`, and a real
  decay rate exists iff `c² ≥ 4αD`. (A complex rate would make the tail oscillate and take
  negative values, which a density cannot do; this is the usual reason the front speed
  is at least `2√(αD)`. That positivity argument is not formalized here.)

**How the formal statements match the source.** Partial derivatives are written as `deriv`
along coordinate lines: `∂u/∂t` at `(x, t)` is `deriv (fun s ↦ u x s) t`, and `∂²u/∂x²` is
`deriv (deriv (fun y ↦ u y t)) x`. We keep the paper's general constants `D` (diffusion) and
`α = F'(0)` rather than normalizing them to `1`. The paper's main theorems (existence of
fronts, convergence of the step datum to the front of minimal speed) are not formalized; see
the entry's notes.
-/

@[expose] public section

open Real

namespace SovietLean.KPP1937

/-- The linearized equation `u_t = D u_xx + α u` holds for `u` at the point `(x, t)`. -/
def LinearizedAt (D α : ℝ) (u : ℝ → ℝ → ℝ) (x t : ℝ) : Prop :=
  deriv (fun s ↦ u x s) t = D * deriv (deriv (fun y ↦ u y t)) x + α * u x t

/-- The nonlinear equation `u_t = D u_xx + F(u)` holds for `u` at the point `(x, t)`. -/
def SolvesAt (D : ℝ) (F : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (x t : ℝ) : Prop :=
  deriv (fun s ↦ u x s) t = D * deriv (deriv (fun y ↦ u y t)) x + F (u x t)

/-- The exponential profile `e^{-μ(x - ct)}` moving to the right at speed `c`. -/
noncomputable def expWave (μ c : ℝ) (x t : ℝ) : ℝ := exp (-μ * (x - c * t))

/-- The dispersion relation: the speed of the exponential with decay rate `μ`. -/
noncomputable def speed (D α μ : ℝ) : ℝ := D * μ + α / μ

lemma expWave_deriv_t (μ c x t : ℝ) :
    deriv (fun s ↦ expWave μ c x s) t = μ * c * expWave μ c x t := by
  have h : HasDerivAt (fun s ↦ -μ * (x - c * s)) (μ * c) t := by
    have := ((hasDerivAt_id t).const_mul c).const_sub x |>.const_mul (-μ)
    simpa using this
  rw [show (fun s ↦ expWave μ c x s) = fun s ↦ exp (-μ * (x - c * s)) from rfl,
    h.exp.deriv, expWave]
  ring

lemma expWave_deriv_x (μ c t : ℝ) :
    deriv (fun y ↦ expWave μ c y t) = fun y ↦ -μ * expWave μ c y t := by
  funext y
  have h : HasDerivAt (fun y ↦ -μ * (y - c * t)) (-μ) y := by
    simpa using ((hasDerivAt_id y).sub_const (c * t)).const_mul (-μ)
  rw [show (fun y ↦ expWave μ c y t) = fun y ↦ exp (-μ * (y - c * t)) from rfl,
    h.exp.deriv, expWave]
  ring

lemma expWave_deriv_xx (μ c x t : ℝ) :
    deriv (deriv (fun y ↦ expWave μ c y t)) x = μ ^ 2 * expWave μ c x t := by
  rw [expWave_deriv_x, deriv_const_mul_field', expWave_deriv_x]
  ring

/-- **Linear analysis.** For `μ > 0`, the exponential `e^{-μ(x - ct)}` satisfies the
linearized equation `u_t = D u_xx + α u` at a point `(x, t)` iff `c = Dμ + α/μ`. -/
theorem linear_exp_solves_iff (D α : ℝ) {μ : ℝ} (hμ : 0 < μ) (c x t : ℝ) :
    LinearizedAt D α (expWave μ c) x t ↔ c = speed D α μ := by
  unfold LinearizedAt speed
  rw [expWave_deriv_t, expWave_deriv_xx]
  have hE : 0 < expWave μ c x t := exp_pos _
  constructor
  · intro h
    have h2 : μ * c = D * μ ^ 2 + α := by
      have := mul_right_cancel₀ hE.ne' (by linarith [h] : μ * c * expWave μ c x t =
        (D * μ ^ 2 + α) * expWave μ c x t)
      exact this
    have h3 : α / μ = c - D * μ := by
      rw [div_eq_iff hμ.ne']
      nlinarith [h2]
    linarith
  · intro h
    rw [h]
    field_simp

/-- **Lower bound on the speed.** For `α, D > 0` and every decay rate `μ > 0`,
`Dμ + α/μ ≥ 2√(αD)`. -/
theorem two_sqrt_le_speed {D α : ℝ} (hD : 0 < D) (hα : 0 < α) {μ : ℝ} (hμ : 0 < μ) :
    2 * √(α * D) ≤ speed D α μ := by
  unfold speed
  have hs : √(α * D) ^ 2 = α * D := sq_sqrt (by positivity)
  have hkey : 2 * √(α * D) * μ ≤ D * μ * μ + α := by
    have h0 : 0 ≤ (D * μ - √(α * D)) ^ 2 := sq_nonneg _
    have h1 : 0 ≤ D * (D * μ * μ + α - 2 * √(α * D) * μ) := by nlinarith [h0, hs]
    nlinarith [(mul_nonneg_iff_of_pos_left hD).1 h1]
  rw [show D * μ + α / μ = (D * μ * μ + α) / μ by field_simp, le_div_iff₀ hμ]
  exact hkey

/-- **The bound is attained** at `μ = √(α/D)`: `c(√(α/D)) = 2√(αD)`. -/
theorem speed_at_optimum {D α : ℝ} (hD : 0 < D) (hα : 0 < α) :
    speed D α (√(α / D)) = 2 * √(α * D) := by
  unfold speed
  have h1 : D * √(α / D) = √(α * D) := by
    rw [show α * D = D ^ 2 * (α / D) by field_simp, sqrt_mul (by positivity),
      sqrt_sq hD.le]
  have h2 : α / √(α / D) = √(α * D) := by
    have hpos : 0 < √(α / D) := sqrt_pos.2 (by positivity)
    rw [div_eq_iff hpos.ne', ← sqrt_mul (by positivity),
      show α * D * (α / D) = α ^ 2 by field_simp, sqrt_sq hα.le]
  rw [h1, h2]
  ring

/-- **Minimal speed of the linearized problem.** Among exponentials `e^{-μ(x - ct)}` with
`μ > 0` solving `u_t = D u_xx + α u`, the least possible speed is `2√(αD)`. -/
theorem minSpeed_isLeast {D α : ℝ} (hD : 0 < D) (hα : 0 < α) :
    IsLeast {c : ℝ | ∃ μ > 0, ∀ x t, LinearizedAt D α (expWave μ c) x t} (2 * √(α * D)) := by
  constructor
  · refine ⟨√(α / D), sqrt_pos.2 (by positivity), fun x t ↦ ?_⟩
    rw [linear_exp_solves_iff D α (sqrt_pos.2 (by positivity)), speed_at_optimum hD hα]
  · rintro c ⟨μ, hμ, h⟩
    rw [(linear_exp_solves_iff D α hμ c 0 0).1 (h 0 0)]
    exact two_sqrt_le_speed hD hα hμ

/-- **No slow exponential fronts.** If `c < 2√(αD)`, no exponentially decaying profile
`e^{-μ(x - ct)}` (`μ > 0`) solves the linearized equation, even at a single point. -/
theorem no_slow_exponential {D α : ℝ} (hD : 0 < D) (hα : 0 < α) {c : ℝ}
    (hc : c < 2 * √(α * D)) {μ : ℝ} (hμ : 0 < μ) (x t : ℝ) :
    ¬ LinearizedAt D α (expWave μ c) x t := by
  intro h
  have := (linear_exp_solves_iff D α hμ c x t).1 h
  have := two_sqrt_le_speed hD hα hμ
  linarith

/-- **Travelling-wave reduction.** If `U` is differentiable and `u(x, t) = U(x - ct)`,
then `u_t = D u_xx + F(u)` holds at `(x, t)` iff `D U''(ξ) + c U'(ξ) + F(U(ξ)) = 0` at
`ξ = x - ct`. (Here `U'' = deriv (deriv U)`; the identity needs no hypothesis on `U'`, but it
is the classical second derivative only when `U'` is differentiable, as for a front.) -/
theorem travelling_wave_iff (D c : ℝ) (F U : ℝ → ℝ) (hU : Differentiable ℝ U)
    (x t : ℝ) :
    SolvesAt D F (fun y s ↦ U (y - c * s)) x t ↔
      D * deriv (deriv U) (x - c * t) + c * deriv U (x - c * t) + F (U (x - c * t)) = 0 := by
  unfold SolvesAt
  have ht : deriv (fun s ↦ U (x - c * s)) t = -c * deriv U (x - c * t) := by
    have hin : HasDerivAt (fun s ↦ x - c * s) (-c) t := by
      simpa using ((hasDerivAt_id t).const_mul c).const_sub x
    rw [show (fun s ↦ U (x - c * s)) = U ∘ (fun s ↦ x - c * s) from rfl,
      ((hU (x - c * t)).hasDerivAt.comp t hin).deriv]
    ring
  have hx1 : deriv (fun y ↦ U (y - c * t)) = fun y ↦ deriv U (y - c * t) := by
    funext y
    exact deriv_comp_sub_const _ (c * t) _
  have hx2 : deriv (deriv (fun y ↦ U (y - c * t))) x = deriv (deriv U) (x - c * t) := by
    rw [hx1]
    exact deriv_comp_sub_const _ (c * t) _
  rw [ht, hx2]
  constructor <;> intro h <;> linarith

/-- **Exponential tails of a front.** Near `U = 0` the profile equation linearizes to
`D U'' + c U' + α U = 0`; the exponential `U(ξ) = e^{-μξ}` solves it (at any one `ξ`, hence
everywhere) iff `Dμ² - cμ + α = 0`. -/
theorem exp_profile_iff (D c α μ ξ : ℝ) :
    D * deriv (deriv fun z ↦ exp (-μ * z)) ξ + c * deriv (fun z ↦ exp (-μ * z)) ξ
        + α * exp (-μ * ξ) = 0 ↔ D * μ ^ 2 - c * μ + α = 0 := by
  have h1 : deriv (fun z ↦ exp (-μ * z)) = fun z ↦ -μ * exp (-μ * z) := by
    funext z
    have : HasDerivAt (fun z ↦ -μ * z) (-μ) z := by
      simpa using (hasDerivAt_id z).const_mul (-μ)
    rw [this.exp.deriv]
    ring
  have h2 : deriv (deriv fun z ↦ exp (-μ * z)) ξ = μ ^ 2 * exp (-μ * ξ) := by
    rw [h1, deriv_const_mul_field', h1]
    ring
  rw [h2, h1]
  have hE : 0 < exp (-μ * ξ) := exp_pos _
  constructor
  · intro h
    have : (D * μ ^ 2 - c * μ + α) * exp (-μ * ξ) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hE.ne'
  · intro h
    have : (D * μ ^ 2 - c * μ + α) * exp (-μ * ξ) = 0 := by rw [h, zero_mul]
    linarith

/-- **Real decay rates exist exactly above the critical speed.** For `D > 0`, the
characteristic equation `Dμ² - cμ + α = 0` has a real root `μ` iff `c² ≥ 4αD`. For `c > 0`
and `α > 0` this is `c ≥ 2√(αD)`, see `sq_ge_iff_ge_two_sqrt`. -/
theorem exists_real_rate_iff {D : ℝ} (hD : 0 < D) (c α : ℝ) :
    (∃ μ : ℝ, D * μ ^ 2 - c * μ + α = 0) ↔ 4 * α * D ≤ c ^ 2 := by
  constructor
  · rintro ⟨μ, hμ⟩
    nlinarith [sq_nonneg (2 * D * μ - c)]
  · intro h
    refine ⟨(c + √(c ^ 2 - 4 * α * D)) / (2 * D), ?_⟩
    set s := √(c ^ 2 - 4 * α * D)
    have hs : s ^ 2 = c ^ 2 - 4 * α * D := sq_sqrt (by linarith)
    have key : D * ((c + s) / (2 * D)) ^ 2 - c * ((c + s) / (2 * D)) + α
        = (s ^ 2 - (c ^ 2 - 4 * α * D)) / (4 * D) := by
      field_simp
      ring
    rw [key, hs, sub_self, zero_div]

/-- For `c ≥ 0` and `α, D ≥ 0`, the condition `c² ≥ 4αD` of `exists_real_rate_iff` is the
speed bound `c ≥ 2√(αD)`. -/
theorem sq_ge_iff_ge_two_sqrt {D α c : ℝ} (hD : 0 ≤ D) (hα : 0 ≤ α) (hc : 0 ≤ c) :
    4 * α * D ≤ c ^ 2 ↔ 2 * √(α * D) ≤ c := by
  have hs : √(α * D) ^ 2 = α * D := sq_sqrt (by positivity)
  have h0 : 0 ≤ √(α * D) := sqrt_nonneg _
  constructor
  · intro h
    nlinarith [sq_nonneg (c - 2 * √(α * D)), sq_nonneg (c + 2 * √(α * D))]
  · intro h
    nlinarith

end SovietLean.KPP1937
