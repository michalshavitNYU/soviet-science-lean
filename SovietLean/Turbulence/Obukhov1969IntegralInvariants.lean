module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.List.Permutation

/-!
# Obukhov (1969), *On integral invariants in systems of hydrodynamic type*

Entry: `entries/turbulence/1969-obukhov-integral-invariants/`.

Obukhov defines a **system of hydrodynamic type** (S.H.T.): a quadratic ODE
`u̇ⁱ = Γⁱ_{λμ} u^λ u^μ` on `ℝⁿ` such that

1. `Γⁱ_{jk} = Γⁱ_{kj}` (symmetry in the lower indices; no loss of generality);
2. the flow preserves phase volume, which is equivalent to `V_j = Γ^λ_{jλ} = 0`;
3. the energy `2E = g_{μν} u^μ u^ν` is conserved, which holds when
   `Γ_{i,jk} + Γ_{j,ki} + Γ_{k,ij} = 0` (indices lowered with `g`).

## Formal version

We work in Obukhov's "Cartesian" coordinates, `g_{ik} = δ_{ik}`, so upper and lower indices
agree and the tensor is a function `Γ : Fin n → Fin n → Fin n → ℝ` with `Γ i j k = Γ_{i,jk}`.
The vector field is `field Γ u i = ∑ j k, Γ i j k * u j * u k`.

| Paper | Lean | Status |
|---|---|---|
| cyclic condition ⇒ `dE/dt = 0` | `energy_identity`, `energy_conserved` | proved |
| volume preservation ⇔ `V_j = 0` | `divergence_eq`, `divergence_free_iff` | proved |
| Boltzmann distribution is stationary | `boltzmann_stationary` | proved |
| canonical `n = 3` system is an S.H.T. | `canonical_cyclic`, `canonical_trace_free` | proved |
| canonical `n = 3` system has a second integral `I` | `rigid_body_integrals` | proved |
| `N = n(n+2)(n-2)/3` independent components | `finrank_shtSpace` | proved |

Two remarks on matching the source.

* With a symmetric tensor, `u̇¹ = 2 Γ_{1,23} u² u³`, so Obukhov's canonical form
  `u̇₁ = p u₂ u₃` corresponds to `Γ_{1,23} = Γ_{1,32} = p/2`. The factor `1/2` is a convention
  and does not affect the condition `p + q + r = 0`.
* The count `N` holds for `n ≥ 2`; for `n = 1` the space is `0`, while the formula gives `-1`.
-/

@[expose] public section

open Finset

namespace SovietLean.Obukhov1969

variable {n : ℕ}

/-- The quadratic vector field `u̇ⁱ = Γⁱ_{λμ} u^λ u^μ`. -/
def field (Γ : Fin n → Fin n → Fin n → ℝ) (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, ∑ k, Γ i j k * u j * u k

/-- Symmetry in the lower indices, condition (5). -/
def IsSymm (Γ : Fin n → Fin n → Fin n → ℝ) : Prop := ∀ i j k, Γ i j k = Γ i k j

/-- The cyclic (energy) condition (11): `Γ_{i,jk} + Γ_{j,ki} + Γ_{k,ij} = 0`. -/
def IsCyclic (Γ : Fin n → Fin n → Fin n → ℝ) : Prop := ∀ i j k, Γ i j k + Γ j k i + Γ k i j = 0

/-- The covector `V_j = Γ^λ_{jλ}` of condition (7). -/
def traceVec (Γ : Fin n → Fin n → Fin n → ℝ) (j : Fin n) : ℝ := ∑ l, Γ l j l

/-- Energy `E = ½ ∑ uᵢ²` (Cartesian coordinates). -/
noncomputable def energy (u : Fin n → ℝ) : ℝ := (∑ i, u i ^ 2) / 2

/-! ### Energy conservation -/

/-- **The cyclic condition kills the energy flux**: `∑ᵢ uᵢ · u̇ⁱ = 0` for every state `u`. -/
theorem energy_identity (Γ : Fin n → Fin n → Fin n → ℝ) (hΓ : IsCyclic Γ) (u : Fin n → ℝ) :
    ∑ i, u i * field Γ u i = 0 := by
  set S := ∑ i, ∑ j, ∑ k, Γ i j k * (u i * u j * u k) with hS
  have hlhs : ∑ i, u i * field Γ u i = S := by
    simp only [field, Finset.mul_sum, hS]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  -- relabel the summation indices cyclically
  have h1 : ∑ i, ∑ j, ∑ k, Γ j k i * (u i * u j * u k) = S := by
    rw [hS, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, ∑ j, ∑ k, Γ k i j * (u i * u j * u k) = S := by
    rw [hS]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have h3 : S + ∑ i, ∑ j, ∑ k, Γ j k i * (u i * u j * u k)
      + ∑ i, ∑ j, ∑ k, Γ k i j * (u i * u j * u k) = 0 := by
    rw [hS, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    linear_combination (u i * u j * u k) * hΓ i j k
  rw [hlhs]; linarith [h1, h2, h3]

/-- **Energy conservation** (condition 3): along any solution of `u̇ = field Γ u`, the energy
is constant. -/
theorem energy_conserved (Γ : Fin n → Fin n → Fin n → ℝ) (hΓ : IsCyclic Γ) (u : ℝ → Fin n → ℝ)
    (hu : ∀ t, HasDerivAt u (field Γ (u t)) t) (t : ℝ) :
    energy (u t) = energy (u 0) := by
  have hd : ∀ t, HasDerivAt (fun s ↦ energy (u s)) 0 t := by
    intro t
    have hi : ∀ i, HasDerivAt (fun s ↦ u s i) (field Γ (u t) i) t :=
      fun i ↦ (hasDerivAt_pi.mp (hu t)) i
    have hsum : HasDerivAt (fun s ↦ ∑ i, u s i ^ 2)
        (∑ i, (2 : ℕ) * u t i ^ (2 - 1) * field Γ (u t) i) t := by
      have := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ (hi i).pow 2)
      simpa using this
    have h0 : (∑ i, (2 : ℕ) * u t i ^ (2 - 1) * field Γ (u t) i) = 0 := by
      have := energy_identity Γ hΓ (u t)
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      rw [show (∑ i, 2 * u t i * field Γ (u t) i) = 2 * ∑ i, u t i * field Γ (u t) i by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring, this, mul_zero]
    rw [h0] at hsum
    simpa [energy] using hsum.div_const 2
  exact is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt)
    (fun t ↦ (hd t).deriv) t 0

/-! ### Volume preservation -/

/-- The partial derivative `∂ u̇ⁱ / ∂ uʲ`, computed along the coordinate line through `u`. -/
theorem hasDerivAt_field_coord (Γ : Fin n → Fin n → Fin n → ℝ) (u : Fin n → ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ ↦ field Γ (u + s • Pi.single j 1) i)
      (∑ k, (Γ i j k + Γ i k j) * u k) 0 := by
  set v : Fin n → ℝ := Pi.single j 1 with hv
  have e1 : ∀ k, ∑ l, Γ i l k * v l = Γ i j k := fun k ↦ by simp [hv, Pi.single_apply]
  have e2 : ∀ l, ∑ k, Γ i l k * v k = Γ i l j := fun l ↦ by simp [hv, Pi.single_apply]
  have hline : ∀ l, HasDerivAt (fun s : ℝ ↦ u l + s * v l) (v l) 0 := fun l ↦ by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v l)).const_add (u l)
  have hfun : (fun s : ℝ ↦ field Γ (u + s • v) i) =
      fun s ↦ ∑ l, ∑ k, Γ i l k * (u l + s * v l) * (u k + s * v k) := by
    funext s; simp [field, smul_eq_mul]
  rw [hfun]
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ ↦ HasDerivAt.fun_sum
    (u := Finset.univ) (fun k _ ↦ ((hline l).const_mul (Γ i l k)).mul (hline k)))
  convert h using 1
  simp only [zero_mul, add_zero, add_mul, Finset.sum_add_distrib]
  have a1 : ∑ l, ∑ k, Γ i l k * v l * u k = ∑ k, Γ i j k * u k := by
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← e1 k, Finset.sum_mul]
  have a2 : ∑ l, ∑ k, Γ i l k * u l * v k = ∑ l, Γ i l j * u l := by
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [← e2 l, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [a1, a2]

/-- The divergence `∑ᵢ ∂u̇ⁱ/∂uⁱ` of the field. -/
def divergence (Γ : Fin n → Fin n → Fin n → ℝ) (u : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ k, (Γ i i k + Γ i k i) * u k

/-- For a symmetric tensor the divergence is `2 V_μ u^μ`. -/
theorem divergence_eq (Γ : Fin n → Fin n → Fin n → ℝ) (hs : IsSymm Γ) (u : Fin n → ℝ) :
    divergence Γ u = 2 * ∑ k, traceVec Γ k * u k := by
  simp only [divergence, traceVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  rw [hs l l k]; ring

/-- **Liouville condition**: the flow is volume preserving (divergence-free at every point)
iff the covector `V_j = Γ^λ_{jλ}` vanishes, condition (6) ⇔ (7). -/
theorem divergence_free_iff (Γ : Fin n → Fin n → Fin n → ℝ) (hs : IsSymm Γ) :
    (∀ u, divergence Γ u = 0) ↔ ∀ j, traceVec Γ j = 0 := by
  constructor
  · intro h j
    have := h (Pi.single j 1)
    rw [divergence_eq Γ hs] at this
    simpa [Pi.single_apply] using this
  · intro h u
    rw [divergence_eq Γ hs]; simp [h]

/-- **The Boltzmann distribution is stationary.** For `σ_Θ(u) = |u|²/Θ`, the Liouville
transport term `u̇ⁱ ∂σ/∂uⁱ = (2/Θ) ∑ uᵢ u̇ⁱ` vanishes identically. -/
theorem boltzmann_stationary (Γ : Fin n → Fin n → Fin n → ℝ) (hΓ : IsCyclic Γ) (Θ : ℝ)
    (u : Fin n → ℝ) : ∑ i, field Γ u i * (2 * u i / Θ) = 0 := by
  have := energy_identity Γ hΓ u
  rw [show ∑ i, field Γ u i * (2 * u i / Θ) = (2 / Θ) * ∑ i, u i * field Γ u i by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring, this, mul_zero]

/-! ### The case `n = 3`: rigid-body dynamics -/

/-- Obukhov's canonical tensor: `Γ_{1,23} = p/2`, `Γ_{2,31} = q/2`, `Γ_{3,12} = r/2`
(symmetrized), all other components zero. Its field is `(p u₂u₃, q u₃u₁, r u₁u₂)`. -/
noncomputable def canonical (p q r : ℝ) : Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k ↦
  if (i, j, k) = (0, 1, 2) ∨ (i, j, k) = (0, 2, 1) then p / 2
  else if (i, j, k) = (1, 2, 0) ∨ (i, j, k) = (1, 0, 2) then q / 2
  else if (i, j, k) = (2, 0, 1) ∨ (i, j, k) = (2, 1, 0) then r / 2
  else 0

theorem field_canonical (p q r : ℝ) (u : Fin 3 → ℝ) :
    field (canonical p q r) u = ![p * u 1 * u 2, q * u 2 * u 0, r * u 0 * u 1] := by
  ext i; fin_cases i <;> simp [field, canonical, Fin.sum_univ_three] <;> ring

theorem canonical_symm (p q r : ℝ) : IsSymm (canonical p q r) := by
  intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [canonical]

/-- The canonical system satisfies the energy condition exactly when `p + q + r = 0`. -/
theorem canonical_cyclic (p q r : ℝ) : IsCyclic (canonical p q r) ↔ p + q + r = 0 := by
  constructor
  · intro h; have := h 0 1 2; simp [canonical] at this; linarith
  · intro h i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [canonical] <;> linarith

/-- The canonical system is volume preserving. -/
theorem canonical_trace_free (p q r : ℝ) (j : Fin 3) : traceVec (canonical p q r) j = 0 := by
  fin_cases j <;> simp [traceVec, canonical, Fin.sum_univ_three]

/-- **Euler's rigid body in Obukhov's canonical form.** If `p + q + r = 0`, solutions of
`u̇₁ = p u₂u₃, u̇₂ = q u₃u₁, u̇₃ = r u₁u₂` conserve both the energy `u₁² + u₂² + u₃²` and
`I = (q - r) u₁² + (r - p) u₂² + (p - q) u₃²`. -/
theorem rigid_body_integrals (p q r : ℝ) (hpqr : p + q + r = 0) (u₁ u₂ u₃ : ℝ → ℝ)
    (h₁ : ∀ t, HasDerivAt u₁ (p * u₂ t * u₃ t) t) (h₂ : ∀ t, HasDerivAt u₂ (q * u₃ t * u₁ t) t)
    (h₃ : ∀ t, HasDerivAt u₃ (r * u₁ t * u₂ t) t) (t : ℝ) :
    u₁ t ^ 2 + u₂ t ^ 2 + u₃ t ^ 2 = u₁ 0 ^ 2 + u₂ 0 ^ 2 + u₃ 0 ^ 2 ∧
    (q - r) * u₁ t ^ 2 + (r - p) * u₂ t ^ 2 + (p - q) * u₃ t ^ 2 =
      (q - r) * u₁ 0 ^ 2 + (r - p) * u₂ 0 ^ 2 + (p - q) * u₃ 0 ^ 2 := by
  constructor
  · have hd : ∀ t, HasDerivAt (fun s ↦ u₁ s ^ 2 + u₂ s ^ 2 + u₃ s ^ 2) 0 t := by
      intro t
      convert (((h₁ t).pow 2).add ((h₂ t).pow 2)).add ((h₃ t).pow 2) using 1
      simp; linear_combination (-2 * u₁ t * u₂ t * u₃ t) * hpqr
    exact is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt) (fun t ↦ (hd t).deriv) t 0
  · have hd : ∀ t, HasDerivAt
        (fun s ↦ (q - r) * u₁ s ^ 2 + (r - p) * u₂ s ^ 2 + (p - q) * u₃ s ^ 2) 0 t := by
      intro t
      convert ((((h₁ t).pow 2).const_mul (q - r)).add (((h₂ t).pow 2).const_mul (r - p))).add
        (((h₃ t).pow 2).const_mul (p - q)) using 1
      simp; ring
    exact is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt) (fun t ↦ (hd t).deriv) t 0

/-! ### Counting independent components -/

/-- The space of dynamical tensors of systems of hydrodynamic type in `n` variables
(for `g = δ`): symmetric, cyclic and trace-free. -/
def shtSpace (n : ℕ) : Submodule ℝ (Fin n → Fin n → Fin n → ℝ) where
  carrier := {Γ | IsSymm Γ ∧ IsCyclic Γ ∧ ∀ j, traceVec Γ j = 0}
  add_mem' := by
    rintro a b ⟨ha₁, ha₂, ha₃⟩ ⟨hb₁, hb₂, hb₃⟩
    refine ⟨fun i j k ↦ ?_, fun i j k ↦ ?_, fun j ↦ ?_⟩
    · simp [ha₁ i j k, hb₁ i j k]
    · simp only [Pi.add_apply]; linarith [ha₂ i j k, hb₂ i j k]
    · simp only [traceVec, Pi.add_apply, Finset.sum_add_distrib]
      rw [show ∑ l, a l j l = 0 from ha₃ j, show ∑ l, b l j l = 0 from hb₃ j, add_zero]
  zero_mem' := ⟨fun _ _ _ ↦ rfl, fun _ _ _ ↦ by simp, fun _ ↦ by simp [traceVec]⟩
  smul_mem' := by
    rintro c a ⟨ha₁, ha₂, ha₃⟩
    refine ⟨fun i j k ↦ ?_, fun i j k ↦ ?_, fun j ↦ ?_⟩
    · simp [ha₁ i j k]
    · simp only [Pi.smul_apply, smul_eq_mul]; linear_combination c * ha₂ i j k
    · simp only [traceVec, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      rw [show ∑ l, a l j l = 0 from ha₃ j, mul_zero]

/-! ### Proof of the count -/

section Count

open Module

/-- Tensors symmetric in the last two indices. -/
def symSpace (n : ℕ) : Submodule ℝ (Fin n → Fin n → Fin n → ℝ) where
  carrier := {Γ | IsSymm Γ}
  add_mem' {a b} ha hb i j k := by simp [ha i j k, hb i j k]
  zero_mem' _ _ _ := rfl
  smul_mem' c a ha i j k := by simp [ha i j k]

/-- Totally symmetric tensors. -/
def IsTotSymm {n : ℕ} (T : Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∀ i j k, T i j k = T j i k ∧ T i j k = T i k j

def totSymSpace (n : ℕ) : Submodule ℝ (Fin n → Fin n → Fin n → ℝ) where
  carrier := {T | IsTotSymm T}
  add_mem' {a b} ha hb i j k := by
    refine ⟨?_, ?_⟩ <;> simp only [Pi.add_apply]
    · rw [(ha i j k).1, (hb i j k).1]
    · rw [(ha i j k).2, (hb i j k).2]
  zero_mem' _ _ _ := ⟨rfl, rfl⟩
  smul_mem' c a ha i j k := by
    refine ⟨?_, ?_⟩ <;> simp only [Pi.smul_apply, smul_eq_mul]
    · rw [(ha i j k).1]
    · rw [(ha i j k).2]

/-! ### Dimension of `symSpace` -/

/-- `symSpace n ≃ (Fin n × Sym2 (Fin n) → ℝ)`. -/
noncomputable def symEquiv (n : ℕ) : symSpace n ≃ₗ[ℝ] (Fin n × Sym2 (Fin n) → ℝ) where
  toFun Γ p := Sym2.lift ⟨fun j k ↦ Γ.1 p.1 j k, fun j k ↦ Γ.2 p.1 j k⟩ p.2
  invFun f := ⟨fun i j k ↦ f (i, s(j, k)), fun i j k ↦ by simp only [Sym2.eq_swap]⟩
  map_add' Γ Δ := by
    funext ⟨i, s⟩; induction s using Sym2.ind; simp
  map_smul' c Γ := by
    funext ⟨i, s⟩; induction s using Sym2.ind; simp
  left_inv Γ := by ext i j k; simp
  right_inv f := by funext ⟨i, s⟩; induction s using Sym2.ind; simp

theorem finrank_symSpace (n : ℕ) : finrank ℝ (symSpace n) = n * (n + 1).choose 2 := by
  rw [(symEquiv n).finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_prod,
    Fintype.card_fin, Sym2.card, Fintype.card_fin]

/-! ### Dimension of `totSymSpace` -/

theorem tot_symm_all {n : ℕ} {T : Fin n → Fin n → Fin n → ℝ} (hT : IsTotSymm T) (a b c : Fin n) :
    T a b c = T b a c ∧ T a b c = T a c b ∧ T a b c = T b c a ∧ T a b c = T c a b ∧
    T a b c = T c b a := by
  have h1 := hT a b c; have h2 := hT b a c; have h3 := hT a c b; have h4 := hT b c a
  have h5 := hT c a b
  refine ⟨h1.1, h1.2, ?_, ?_, ?_⟩
  · rw [h1.1, h2.2]
  · rw [h1.2, h3.1]
  · rw [h1.1, h2.2, h4.1]

theorem perm3 {n : ℕ} {T : Fin n → Fin n → Fin n → ℝ} (hT : IsTotSymm T) {a b c a' b' c' : Fin n}
    (h : List.Perm [a, b, c] [a', b', c']) : T a b c = T a' b' c' := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := tot_symm_all hT a b c
  have ha' : a' ∈ [a, b, c] := h.symm.subset (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
  rcases ha' with rfl | rfl | rfl
  · have h2 : List.Perm [b, c] [b', c'] := (List.perm_cons _).1 h
    rcases List.pair_perm.1 h2 with h3 | h3 <;> simp only [List.cons.injEq, and_true] at h3 <;>
      obtain ⟨rfl, rfl⟩ := h3
    · rfl
    · exact s2
  · have h1 : List.Perm [a', a, c] [a', b', c'] := (List.Perm.swap a a' [c]).trans h
    have h2 : List.Perm [a, c] [b', c'] := (List.perm_cons _).1 h1
    rcases List.pair_perm.1 h2 with h3 | h3 <;> simp only [List.cons.injEq, and_true] at h3 <;>
      obtain ⟨rfl, rfl⟩ := h3
    · exact s1
    · exact s3
  · have h1 : List.Perm [a', a, b] [a', b', c'] :=
      (List.perm_middle (l₁ := [a, b]) (l₂ := []) (a := a')).symm.trans h
    have h2 : List.Perm [a, b] [b', c'] := (List.perm_cons _).1 h1
    rcases List.pair_perm.1 h2 with h3 | h3 <;> simp only [List.cons.injEq, and_true] at h3 <;>
      obtain ⟨rfl, rfl⟩ := h3
    · exact s4
    · exact s5

/-- Evaluate a function on 3-element lists, zero elsewhere. -/
def on3 {α : Type*} (T : α → α → α → ℝ) : List α → ℝ
  | [a, b, c] => T a b c
  | _ => 0

theorem on3_perm {n : ℕ} {T : Fin n → Fin n → Fin n → ℝ} (hT : IsTotSymm T) :
    ∀ l l' : List (Fin n), List.Perm l l' → on3 T l = on3 T l' := by
  intro l l' h
  have hl := h.length_eq
  match l, l', h, hl with
  | [a, b, c], [a', b', c'], h, _ => exact perm3 hT h
  | [], [], _, _ => rfl
  | [_], [_], _, _ => rfl
  | [_, _], [_, _], _, _ => rfl
  | _ :: _ :: _ :: _ :: _, _ :: _ :: _ :: _ :: _, _, _ => rfl

/-- `Sym (Fin n) 3 → ℝ` maps onto totally symmetric tensors. -/
noncomputable def symFunToTot (n : ℕ) : (Sym (Fin n) 3 → ℝ) →ₗ[ℝ] totSymSpace n where
  toFun f := ⟨fun i j k ↦ f (i ::ₛ j ::ₛ k ::ₛ Sym.nil), fun i _ _ ↦
    ⟨congrArg f (Sym.cons_swap _ _ _), congrArg f (congrArg (i ::ₛ ·) (Sym.cons_swap _ _ _))⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sym3_eq {n : ℕ} (s : Sym (Fin n) 3) : ∃ a b c : Fin n, s = a ::ₛ b ::ₛ c ::ₛ Sym.nil := by
  obtain ⟨m, hm⟩ := s
  induction m using Quot.ind with
  | mk l =>
    match l, hm with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩

theorem symFunToTot_bijective (n : ℕ) : Function.Bijective (symFunToTot n) := by
  constructor
  · intro f g hfg
    funext s
    obtain ⟨a, b, c, rfl⟩ := sym3_eq s
    have := congrArg (fun T : totSymSpace n ↦ T.1 a b c) hfg
    exact this
  · intro T
    refine ⟨fun s ↦ Quot.liftOn s.1 (on3 T.1) (on3_perm T.2), ?_⟩
    ext i j k
    rfl

theorem finrank_totSymSpace (n : ℕ) : finrank ℝ (totSymSpace n) = (n + 2).choose 3 := by
  rw [← (LinearEquiv.ofBijective _ (symFunToTot_bijective n)).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Sym.card_sym_eq_choose, Fintype.card_fin]
  rfl

/-! ### The map `Γ ↦ (cyclic sum, trace)` -/

/-- The cyclic sum `Γ_{i,jk} + Γ_{j,ki} + Γ_{k,ij}` of a tensor symmetric in `j, k` is totally
symmetric. -/
noncomputable def cycMap (n : ℕ) : symSpace n →ₗ[ℝ] totSymSpace n where
  toFun Γ := ⟨fun i j k ↦ Γ.1 i j k + Γ.1 j k i + Γ.1 k i j, fun i j k ↦ by
    have h : IsSymm Γ.1 := Γ.2
    refine ⟨?_, ?_⟩
    · beta_reduce; rw [h j i k, h i k j, h k j i]; ring
    · beta_reduce; rw [h i k j, h k j i, h j i k]; ring⟩
  map_add' Γ Δ := by ext i j k; simp; ring
  map_smul' c Γ := by ext i j k; simp; ring

noncomputable def trMap (n : ℕ) : symSpace n →ₗ[ℝ] (Fin n → ℝ) where
  toFun Γ := traceVec Γ.1
  map_add' Γ Δ := by funext j; simp [traceVec, Finset.sum_add_distrib]
  map_smul' c Γ := by funext j; simp [traceVec, Finset.mul_sum]

noncomputable def Φ (n : ℕ) : symSpace n →ₗ[ℝ] totSymSpace n × (Fin n → ℝ) :=
  (cycMap n).prod (trMap n)

/-- A tensor with zero cyclic sum and trace `e_j`: supported on the index pair `{j, l}`. -/
noncomputable def E {n : ℕ} (j l : Fin n) : Fin n → Fin n → Fin n → ℝ := fun i a b ↦
  if i = l ∧ a = j ∧ b = l then 1
  else if i = l ∧ a = l ∧ b = j then 1
  else if i = j ∧ a = l ∧ b = l then -2 else 0

theorem E_symm {n : ℕ} {j l : Fin n} (hl : l ≠ j) : IsSymm (E j l) := by
  intro i a b; simp only [E]; split_ifs <;> simp_all

theorem E_cyc {n : ℕ} {j l : Fin n} (hl : l ≠ j) (i a b : Fin n) :
    E j l i a b + E j l a b i + E j l b i a = 0 := by
  simp only [E]; split_ifs <;> simp_all <;> norm_num

theorem E_trace {n : ℕ} {j l : Fin n} (hl : l ≠ j) : traceVec (E j l) = Pi.single j 1 := by
  funext m
  simp only [traceVec, E, Pi.single_apply]
  rw [Finset.sum_eq_single l]
  · by_cases hm : m = j
    · simp [hm]
    · simp [hm, hl]
  · intro x _ hx; simp [hx]
  · simp

theorem Φ_surjective (n : ℕ) (hn : 2 ≤ n) : Function.Surjective (Φ n) := by
  -- for each `j`, some `l ≠ j`
  have hl : ∀ j : Fin n, ∃ l : Fin n, l ≠ j := by
    intro j
    by_cases hj : j.val = 0
    · exact ⟨⟨1, by omega⟩, fun h ↦ by simp [Fin.ext_iff] at h; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h ↦ by simp [Fin.ext_iff] at h; omega⟩
  choose l hl using hl
  let Ej : Fin n → symSpace n := fun j ↦ ⟨E j (l j), E_symm (hl j)⟩
  have hEj : ∀ j, Φ n (Ej j) = (0, Pi.single j 1) := by
    intro j
    refine Prod.ext ?_ ?_
    · ext i a b; exact E_cyc (hl j) i a b
    · exact E_trace (hl j)
  -- the section `T ↦ T/3`
  let s3 : totSymSpace n → symSpace n := fun T ↦ ⟨fun i j k ↦ T.1 i j k / 3,
    fun i j k ↦ by beta_reduce; rw [(T.2 i j k).2]⟩
  have hs3 : ∀ T, (Φ n (s3 T)).1 = T := by
    intro T; ext i j k
    change T.1 i j k / 3 + T.1 j k i / 3 + T.1 k i j / 3 = T.1 i j k
    obtain ⟨_, _, h3, h4, _⟩ := tot_symm_all T.2 i j k
    rw [← h3, ← h4]; ring
  rintro ⟨T, v⟩
  let w : Fin n → ℝ := v - (Φ n (s3 T)).2
  refine ⟨s3 T + ∑ j, w j • Ej j, ?_⟩
  rw [map_add, map_sum]
  simp only [map_smul, hEj]
  refine Prod.ext ?_ ?_
  · simp [hs3, Prod.fst_sum]
  · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd]
    have : ∑ j, w j • (Pi.single j (1 : ℝ) : Fin n → ℝ) = w := by
      funext m; simp [Finset.sum_apply, Pi.single_apply]
    rw [this]; simp [w]

/-! ### Putting it together -/

theorem map_ker_Φ (n : ℕ) : (LinearMap.ker (Φ n)).map (symSpace n).subtype = shtSpace n := by
  ext Γ
  simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 := congrArg Prod.fst hx
    have h2 := congrArg Prod.snd hx
    refine ⟨x.2, fun i j k ↦ ?_, fun j ↦ ?_⟩
    · exact congrArg (fun T : totSymSpace n ↦ T.1 i j k) h1
    · exact congrFun h2 j
  · rintro ⟨hs, hc, ht⟩
    refine ⟨⟨Γ, hs⟩, Prod.ext ?_ ?_, rfl⟩
    · ext i j k; exact hc i j k
    · funext j; exact ht j

/-- **Obukhov's count**: for `n ≥ 2` the dynamical tensor has `N = n(n+2)(n-2)/3`
independent components.

Proof: tensors symmetric in `j, k` form a space of dimension `n·C(n+1, 2)`. The map
`Γ ↦ (cyclic sum, trace)` sends it onto (totally symmetric tensors) × `ℝⁿ`, of dimension
`C(n+2, 3) + n` (onto needs `n ≥ 2`), and its kernel is `shtSpace n`. Rank–nullity gives
`N = n·C(n+1,2) - C(n+2,3) - n = n(n+2)(n-2)/3`. -/
theorem finrank_shtSpace (n : ℕ) (hn : 2 ≤ n) :
    3 * (finrank ℝ (shtSpace n) : ℤ) = n * (n + 2) * (n - 2) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (Φ n)
  rw [LinearMap.range_eq_top.2 (Φ_surjective n hn), finrank_top, Module.finrank_prod,
    finrank_totSymSpace, Module.finrank_fin_fun, finrank_symSpace,
    (Submodule.equivMapOfInjective _ (symSpace n).injective_subtype _).finrank_eq,
    map_ker_Φ] at hrn
  have c2 : 2 * (n + 1).choose 2 = (n + 1) * n := by
    have h := Nat.descFactorial_eq_factorial_mul_choose (n + 1) 2
    simp [Nat.descFactorial, Nat.factorial] at h
    linarith
  have c3 : 6 * (n + 2).choose 3 = (n + 2) * (n + 1) * n := by
    have h := Nat.descFactorial_eq_factorial_mul_choose (n + 2) 3
    simp [Nat.descFactorial, Nat.factorial] at h
    linarith
  have hq : (3 * (finrank ℝ (shtSpace n) : ℚ)) = n * (n + 2) * (n - 2) := by
    have e1 : (2 * (n + 1).choose 2 : ℚ) = (n + 1) * n := by exact_mod_cast c2
    have e2 : (6 * (n + 2).choose 3 : ℚ) = (n + 2) * (n + 1) * n := by exact_mod_cast c3
    have e3 : ((n * (n + 1).choose 2 : ℕ) : ℚ) =
        (((n + 2).choose 3 + n + finrank ℝ (shtSpace n) : ℕ) : ℚ) := by rw [hrn]
    push_cast at e3
    linear_combination (3 * (n : ℚ) / 2) * e1 - (1 / 2) * e2 - 3 * e3
  exact_mod_cast hq

end Count

end SovietLean.Obukhov1969
