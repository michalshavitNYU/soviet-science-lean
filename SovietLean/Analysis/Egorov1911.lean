module

public import Mathlib.MeasureTheory.Function.Egorov
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Egorov (1911), *Sur les suites de fonctions mesurables*

Entry: `entries/analysis/1911-egorov-suites-fonctions-mesurables/`.

Egorov's three-page note in the *Comptes rendus* (t. 152, séance du 30 janvier 1911,
pp. 244–246) proves what is now called **Egorov's theorem**:

> *Si l'on a une suite de fonctions mesurables convergente pour tous les points d'un intervalle
> AB sauf, peut-être, les points d'un ensemble de mesure nulle, on pourra toujours enlever de
> l'intervalle AB un ensemble de mesure η aussi petite qu'on voudra et tel que pour l'ensemble
> complémentaire [de mesure = m(AB) − η] la suite est uniformément convergente.*

The note's notation: `f₁, f₂, …, fₙ, …` measurable on an interval `AB`, converging to a limit
`f(x)` outside a null set. On the way it uses

* (1) convergence in measure (attributed to Borel and F. Riesz): the measure `m(n, ε)` of the set
  where `|f(x) − fₙ(x)| > ε` tends to `0`;
* Lebesgue's proposition: the measure `μ(n, ε)` of the set `Eₙ` where `|f(x) − f_m(x)| ≥ ε` for
  *some* `m ≥ n` tends to `0`;
* Weyl's functions `R̄ₙ(x)`, the supremum of `|f(x) − f_m(x)|` over `m ≥ n`, with (3)
  `R̄₁ ≥ R̄₂ ≥ …`, (4) `|f(x) − f_m(x)| ≤ R̄ₙ(x)` for `m ≥ n`, `R̄ₙ(x) → 0` at points of
  convergence, and footnote (4): `R̄ₙ` is measurable.

## Formal version

| Paper | Lean | Status |
|---|---|---|
| Théorème (Egorov's theorem) | `egorov` | proved |
| (1): `m(n, ε) → 0` | `measure_gt_tendsto_zero` | proved |
| Lebesgue's proposition: `μ(n, ε) → 0` | `measure_tail_tendsto_zero` | proved |
| (3): `R̄ₙ` is nonincreasing in `n` | `Rbar_antitone` | proved |
| (4): `|f − f_m| ≤ R̄ₙ` for `m ≥ n` | `le_Rbar` | proved |
| `R̄ₙ(x) → 0` at points of convergence | `Rbar_tendsto_zero` | proved |
| footnote (4): `R̄ₙ` is measurable | `measurable_Rbar` | proved |

How the formal statements match the paper.

* **Names.** The sequence `fₙ` is `f n : ℝ → ℝ`; the paper's limit `f` is called `g`, to keep
  `f` for the sequence. The interval `AB` is `Set.Icc a b`; whether its endpoints are included
  does not matter (they form a null set). "Mesure" is Lebesgue measure, Mathlib's `volume` on `ℝ`.
* **Hypotheses.** "convergente … pour tous les points … sauf, peut-être, les points d'un ensemble
  de mesure nulle" is `∀ᵐ x, x ∈ Icc a b → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))`. The `fₙ`
  are assumed `Measurable` (Borel measurable). This is no loss: a Lebesgue-measurable function
  agrees with a Borel one outside a null set, and the exceptional null set can be absorbed into
  the set removed. **The limit `g` is not assumed measurable**: the proof replaces it by a
  measurable function that agrees with it off a null set, and adds that null set to the removed
  set.
* **Conclusion of `egorov`.** For each `η > 0` there is a measurable `E ⊆ AB` with
  `volume E ≤ η` on whose complement in `AB` the convergence is uniform (`TendstoUniformlyOn`),
  and the complement has measure at least `m(AB) − η`, the bracket in the theorem. The paper
  writes "de mesure η aussi petite qu'on voudra"; we give the bound `≤ η`, which is what
  "arbitrarily small" means.
* **(1) and Lebesgue's proposition** are stated with the paper's sets: `ε < |g x − f n x|` for
  `m(n, ε)` and `∃ m ≥ n, ε ≤ |g x − f m x|` for `Eₙ`. Lebesgue measure is applied to them as an
  outer measure, so no measurability of these sets is needed. The proofs go the other way from
  the paper: we derive both from Egorov's theorem, while Egorov derives Lebesgue's proposition
  from (1) and then the theorem.
* **`R̄ₙ`** is `Rbar f g n x = ⨆ m ≥ n, ENNReal.ofReal |g x − f m x|`, a supremum in `[0, ∞]`,
  so it is defined even where the sequence `(2)` is unbounded. Its measurability needs `g`
  measurable, which in the paper follows from `g` being an almost-everywhere limit; we assume it.

The proof of `egorov` cites Mathlib's `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`
(`Mathlib/MeasureTheory/Function/Egorov.lean`, by Kexing Ying), whose proof follows Egorov's:
for each `i` a tail set where the sequence is far from the limit is chosen with small measure,
and these measures are summed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace SovietLean.Egorov1911

/-- Egorov's theorem with the bound on the removed set given in `[0, ∞]`; the main theorem
`egorov` below restates it for a real `η > 0`. -/
theorem egorov_ennreal (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a b : ℝ) (hf : ∀ n, Measurable (f n))
    (hfg : ∀ᵐ x, x ∈ Icc a b → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ E ⊆ Icc a b, MeasurableSet E ∧ volume E ≤ δ ∧
      TendstoUniformlyOn f g atTop (Icc a b \ E) := by
  -- a measurable null set `N` outside which the sequence converges on `AB`
  set P : ℝ → Prop := fun x ↦ x ∈ Icc a b → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))
  have hP : volume {x | ¬ P x} = 0 := ae_iff.1 hfg
  set N := toMeasurable volume {x | ¬ P x}
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by rw [measure_toMeasurable]; exact hP
  have hPN : ∀ x, x ∉ N → P x := fun x hx ↦ by
    by_contra h; exact hx (subset_toMeasurable _ _ h)
  -- cut the sequence and the limit down to `S = AB \ N`, where convergence is everywhere
  set S := Icc a b \ N
  have hS : MeasurableSet S := measurableSet_Icc.diff hNm
  set F : ℕ → ℝ → ℝ := fun n ↦ S.indicator (f n)
  set G : ℝ → ℝ := S.indicator g
  have hFG : ∀ x, Tendsto (fun n ↦ F n x) atTop (𝓝 (G x)) := by
    intro x
    by_cases hx : x ∈ S
    · simp only [F, G, indicator_of_mem hx]
      exact hPN x hx.2 hx.1
    · simp only [F, G, indicator_of_notMem hx]
      exact tendsto_const_nhds
  have hFm : ∀ n, Measurable (F n) := fun n ↦ (hf n).indicator hS
  have hGm : Measurable G := measurable_of_tendsto_metrizable hFm (tendsto_pi_nhds.2 hFG)
  obtain ⟨t, htAB, htm, htδ, hunif⟩ :=
    tendstoUniformlyOn_of_ae_tendsto (μ := volume) (fun n ↦ (hFm n).stronglyMeasurable)
      hGm.stronglyMeasurable measurableSet_Icc measure_Icc_lt_top.ne
      (ae_of_all _ fun x _ ↦ hFG x) hδ
  refine ⟨t ∪ (N ∩ Icc a b), union_subset htAB inter_subset_right,
    htm.union (hNm.inter measurableSet_Icc), ?_, ?_⟩
  · calc volume (t ∪ (N ∩ Icc a b)) ≤ volume t + volume (N ∩ Icc a b) := measure_union_le _ _
      _ ≤ δ + 0 := add_le_add htδ (le_of_le_of_eq (measure_mono inter_subset_left) hN0)
      _ = δ := add_zero δ
  · have hsub : Icc a b \ (t ∪ (N ∩ Icc a b)) ⊆ Icc a b \ t :=
      sdiff_subset_sdiff_right subset_union_left
    have hinS : ∀ x ∈ Icc a b \ (t ∪ (N ∩ Icc a b)), x ∈ S := fun x hx ↦
      ⟨hx.1, fun hxN ↦ hx.2 (Or.inr ⟨hxN, hx.1⟩)⟩
    refine ((hunif.mono hsub).congr (Eventually.of_forall fun n x hx ↦ ?_)).congr_right
      (fun x hx ↦ ?_)
    · simp only [F, indicator_of_mem (hinS x hx)]
    · simp only [G, indicator_of_mem (hinS x hx)]

/-- **Egorov's theorem** (the note's *Théorème*). If measurable functions `fₙ` converge to `g` at
every point of the interval `AB = [a, b]` outside a set of measure zero, then for every `η > 0`
one can remove from `AB` a measurable set `E` of measure at most `η` such that on the
complement, of measure at least `m(AB) − η`, the sequence converges uniformly. -/
theorem egorov (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a b : ℝ) (hf : ∀ n, Measurable (f n))
    (hfg : ∀ᵐ x, x ∈ Icc a b → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    {η : ℝ} (hη : 0 < η) :
    ∃ E ⊆ Icc a b, MeasurableSet E ∧ volume E ≤ ENNReal.ofReal η ∧
      TendstoUniformlyOn f g atTop (Icc a b \ E) ∧
      ENNReal.ofReal (b - a) - ENNReal.ofReal η ≤ volume (Icc a b \ E) := by
  obtain ⟨E, hEAB, hEm, hEη, hunif⟩ :=
    egorov_ennreal f g a b hf hfg (δ := ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)
  refine ⟨E, hEAB, hEm, hEη, hunif, ?_⟩
  calc ENNReal.ofReal (b - a) - ENNReal.ofReal η ≤ volume (Icc a b) - volume E := by
        rw [Real.volume_Icc]; exact tsub_le_tsub_left hEη _
    _ ≤ volume (Icc a b \ E) := le_measure_sdiff

/-- **Lebesgue's proposition** quoted in the note: the measure `μ(n, ε)` of the set `Eₙ` of
points of `AB` at which `|f(x) − f_m(x)| ≥ ε` for at least one `m ≥ n` tends to `0`. -/
theorem measure_tail_tendsto_zero (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ n, Measurable (f n))
    (hfg : ∀ᵐ x, x ∈ Icc a b → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ volume {x | x ∈ Icc a b ∧ ∃ m ≥ n, ε ≤ |g x - f m x|}) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨E, -, -, hEδ, hunif⟩ := egorov_ennreal f g a b hf hfg hδ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hunif ε hε)
  refine eventually_atTop.2 ⟨N, fun n hn ↦ le_trans (measure_mono ?_) hEδ⟩
  rintro x ⟨hxAB, m, hmn, hm⟩
  by_contra hxE
  have := hN m (hn.trans hmn) x ⟨hxAB, hxE⟩
  rw [Real.dist_eq] at this
  linarith

/-- Eq. (1), **convergence in measure** (Borel, F. Riesz): the measure `m(n, ε)` of the set of
points of `AB` at which `|f(x) − fₙ(x)| > ε` tends to `0`. -/
theorem measure_gt_tendsto_zero (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ n, Measurable (f n))
    (hfg : ∀ᵐ x, x ∈ Icc a b → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ volume {x | x ∈ Icc a b ∧ ε < |g x - f n x|}) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (measure_tail_tendsto_zero f g a b hf hfg hε) (fun _ ↦ bot_le)
    (fun n ↦ measure_mono fun _ hx ↦ ⟨hx.1, n, le_rfl, hx.2.le⟩)

/-- Weyl's function `R̄ₙ(x)`: the supremum ("limite supérieure") of the numbers (2)
`|f(x) − fₙ(x)|, |f(x) − fₙ₊₁(x)|, …`, taken in `[0, ∞]`. -/
noncomputable def Rbar (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ m ≥ n, ENNReal.ofReal |g x - f m x|

/-- Eq. (3): `R̄₁(x) ≥ R̄₂(x) ≥ … ≥ R̄ₙ(x) ≥ R̄ₙ₊₁(x) ≥ …`. -/
theorem Rbar_antitone (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (x : ℝ) :
    Antitone fun n ↦ Rbar f g n x := fun _ _ h ↦
  iSup₂_le fun m hm ↦ le_iSup₂ (f := fun m (_ : m ≥ _) ↦ ENNReal.ofReal |g x - f m x|) m
    (h.trans hm)

/-- Eq. (4): `|f(x) − f_m(x)| ≤ R̄ₙ(x)` for `m = n, n + 1, …`. -/
theorem le_Rbar (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (x : ℝ) {n m : ℕ} (hm : n ≤ m) :
    ENNReal.ofReal |g x - f m x| ≤ Rbar f g n x :=
  le_iSup₂ (f := fun m (_ : m ≥ n) ↦ ENNReal.ofReal |g x - f m x|) m hm

/-- At every point of convergence, `lim R̄ₙ(x) = 0`. -/
theorem Rbar_tendsto_zero (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (x : ℝ)
    (hx : Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ Rbar f g n x) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδt : δ = ⊤
  · exact Eventually.of_forall fun _ ↦ hδt ▸ le_top
  have hδr : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδt
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hx _ hδr
  refine eventually_atTop.2 ⟨N, fun n hn ↦ iSup₂_le fun m hm ↦ ?_⟩
  have h := hN m (hn.trans hm)
  rw [Real.dist_eq, abs_sub_comm] at h
  calc ENNReal.ofReal |g x - f m x| ≤ ENNReal.ofReal δ.toReal := ENNReal.ofReal_le_ofReal h.le
    _ = δ := ENNReal.ofReal_toReal hδt

/-- Footnote (4): `R̄ₙ` is measurable (here for a measurable limit `g`). -/
theorem measurable_Rbar (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (hf : ∀ n, Measurable (f n))
    (hg : Measurable g) (n : ℕ) : Measurable (Rbar f g n) := by
  unfold Rbar
  exact Measurable.iSup fun m ↦ Measurable.iSup fun _ ↦
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hg.sub (hf m)))

end SovietLean.Egorov1911
