module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.Perfect
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Luzin (1912), *Sur les propriétés des fonctions mesurables*

Entry: `entries/analysis/1912-luzin-proprietes-fonctions-mesurables/`.

Luzin's three-page note in the *Comptes Rendus* (t. 154, 1912, pp. 1688–1690) announces what is
now called **Luzin's theorem**. For a function `f` on the interval `0 ≤ x ≤ 1` he calls the
following the **"C-property"** (property (C) of the note):

> for every `ε > 0` there is a perfect, nowhere dense set `P` in the interval such that
> 1° `f` is continuous on `P` (relatively to `P`), and 2° the measure of `P` exceeds `1 - ε`.

He proves that a limit almost everywhere of functions with the C-property has the C-property
(via Egorov's theorem), and states the **general theorem**: *every measurable function on
`0 ≤ x ≤ 1` has the C-property; conversely, every function with the C-property is measurable.*
As a consequence: *every measurable function on `[0, 1]` is the sum of a series of polynomials
converging absolutely to it at every point outside a set of measure zero.*

## Formal version

* The interval `0 ≤ x ≤ 1` is `Set.Icc (0 : ℝ) 1`; "measure" is Lebesgue measure `volume`.
* A function "defined on the interval" is a function `f : ℝ → ℝ`; only its values on
  `[0, 1]` matter in every statement below. Luzin's functions are real-valued; the note's general
  theorem does not mention infinite values (his later Theorem II assumes `f` finite a.e.).
* "Measurable" (in the sense of Lebesgue) is `AEMeasurable f (volume.restrict (Icc 0 1))`:
  `f` agrees a.e. on `[0, 1]` with a Borel function, which for real-valued functions is exactly
  Lebesgue measurability on `[0, 1]`.
* "Perfect" is Mathlib's `Perfect` (closed, no isolated points). "Non dense" (*non dense*,
  in the usage of Baire and Borel) is "nowhere dense", Mathlib's `IsNowhereDense`.
* "Continuous on `P` relatively to `P`" is `ContinuousOn f P`.
* "The measure of `P` exceeds `1 - ε`" is `ENNReal.ofReal (1 - ε) < volume P`.

| Note | Lean | |
|---|---|---|
| definition of the C-property | `CProperty` | definition |
| general theorem: measurable ⇒ C-property | `cProperty_of_aemeasurable` | proved |
| converse: C-property ⇒ measurable | `aemeasurable_of_cProperty` | proved |
| both together | `aemeasurable_iff_cProperty` | proved |
| a.e. limit of C-functions is a C-function | `cProperty_of_tendsto` | proved |
| `f = g` off measure `< ε`, `g` continuous (modern) | `exists_continuous_eq_off` | proved |
| series of polynomials converging absolutely a.e. to `f` | `exists_polynomial_series` | proved |

Mathlib (v4.35) has no Luzin theorem, so the proofs are written here. They are not Luzin's (he
goes through Egorov's theorem and Baire classes); they use the textbook argument from the
regularity of Lebesgue measure: for each set `U` in a countable basis of `ℝ`, squeeze
`f⁻¹(U)` and its complement between closed sets up to a small error; on the intersection `K` of
all these closed sets, `f⁻¹(U) ∩ K` is relatively open. Removing small balls around the
rationals makes the set nowhere dense, and the Cantor–Bendixson theorem
(`exists_countable_union_perfect_of_isClosed`) removes a countable, hence null, part to make it
perfect. The polynomial series uses Weierstrass's theorem (`exists_polynomial_near_continuousMap`),
Tietze's extension theorem and the Borel–Cantelli lemma (`ae_eventually_notMem`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace SovietLean.Luzin1912

/-- Luzin's **C-property** of a function `f` on `0 ≤ x ≤ 1`: for every `ε > 0` there is a
perfect, nowhere dense set `P ⊆ [0, 1]` on which `f` is continuous (relatively to `P`) and whose
measure exceeds `1 - ε`. -/
def CProperty (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ P ⊆ Icc (0 : ℝ) 1, Perfect P ∧ IsNowhereDense P ∧ ContinuousOn f P ∧
    ENNReal.ofReal (1 - ε) < volume P

/-- Core of Luzin's theorem for a Borel function: a closed set `K` of almost full measure in
`[0, 1]` on which `g` is continuous. -/
lemma exists_isClosed_continuousOn_of_measurable {g : ℝ → ℝ} (hg : Measurable g)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K, IsClosed K ∧ volume (Icc (0 : ℝ) 1 \ K) < ε ∧ ContinuousOn g K := by
  set I := Icc (0 : ℝ) 1
  set B := TopologicalSpace.countableBasis ℝ
  have : Countable B := (TopologicalSpace.countable_countableBasis ℝ).to_subtype
  obtain ⟨δ, δpos, hδ⟩ := ENNReal.exists_pos_sum_of_countable' hε B
  have hIfin : volume I ≠ ∞ := measure_Icc_lt_top.ne
  have key : ∀ b : B, ∃ F G : Set ℝ, F ⊆ g ⁻¹' b ∧ G ⊆ (g ⁻¹' b)ᶜ ∧ IsClosed F ∧ IsClosed G ∧
      volume (I \ (F ∪ G)) < δ b := by
    intro b
    have hbm : MeasurableSet (g ⁻¹' (b : Set ℝ)) :=
      hg ((TopologicalSpace.isOpen_of_mem_countableBasis b.2).measurableSet)
    have h2 : δ b / 2 ≠ 0 := (ENNReal.half_pos (δpos b).ne').ne'
    obtain ⟨F, hFA, hFc, hF⟩ := (hbm.inter measurableSet_Icc).exists_isClosed_sdiff_lt
      (μ := volume) (measure_mono inter_subset_right |>.trans_lt measure_Icc_lt_top).ne h2
    obtain ⟨G, hGA, hGc, hG⟩ := (hbm.compl.inter measurableSet_Icc).exists_isClosed_sdiff_lt
      (μ := volume) (measure_mono inter_subset_right |>.trans_lt measure_Icc_lt_top).ne h2
    refine ⟨F, G, hFA.trans inter_subset_left, hGA.trans inter_subset_left, hFc, hGc, ?_⟩
    calc volume (I \ (F ∪ G))
        ≤ volume ((g ⁻¹' b ∩ I) \ F ∪ ((g ⁻¹' b)ᶜ ∩ I) \ G) := by
          refine measure_mono fun x hx => ?_
          by_cases h : x ∈ g ⁻¹' b
          · exact Or.inl ⟨⟨h, hx.1⟩, fun hF => hx.2 (Or.inl hF)⟩
          · exact Or.inr ⟨⟨h, hx.1⟩, fun hG => hx.2 (Or.inr hG)⟩
      _ ≤ volume ((g ⁻¹' b ∩ I) \ F) + volume (((g ⁻¹' b)ᶜ ∩ I) \ G) := measure_union_le _ _
      _ < δ b / 2 + δ b / 2 := ENNReal.add_lt_add hF hG
      _ = δ b := ENNReal.add_halves _
  choose F G hFA hGA hFc hGc hFG using key
  refine ⟨⋂ b, (F b ∪ G b), isClosed_iInter fun b => (hFc b).union (hGc b), ?_, ?_⟩
  · rw [sdiff_iInter]
    calc volume (⋃ b, I \ (F b ∪ G b)) ≤ ∑' b, volume (I \ (F b ∪ G b)) := measure_iUnion_le _
      _ ≤ ∑' b, δ b := ENNReal.tsum_le_tsum fun b => (hFG b).le
      _ < ε := hδ
  · rw [continuousOn_iff_continuous_domRestrict,
      (TopologicalSpace.isBasis_countableBasis ℝ).continuous_iff]
    intro s hs
    have : (⋂ b, (F b ∪ G b)).domRestrict g ⁻¹' s = Subtype.val ⁻¹' (G ⟨s, hs⟩)ᶜ := by
      ext ⟨x, hx⟩
      have hx' := mem_iInter.1 hx ⟨s, hs⟩
      simp only [mem_preimage, Set.domRestrict_apply, mem_compl_iff]
      constructor
      · intro hgx hG
        exact hGA ⟨s, hs⟩ hG hgx
      · intro hG
        rcases hx' with hF | hG'
        · exact hFA ⟨s, hs⟩ hF
        · exact absurd hG' hG
    rw [this]
    exact (hGc _).isOpen_compl.preimage continuous_subtype_val

/-- Luzin's theorem for an a.e.-measurable function, closed-set form. -/
lemma exists_isClosed_continuousOn {f : ℝ → ℝ}
    (hf : AEMeasurable f (volume.restrict (Icc (0 : ℝ) 1))) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ Icc (0 : ℝ) 1, IsClosed K ∧ volume (Icc (0 : ℝ) 1 \ K) < ε ∧ ContinuousOn f K := by
  set I := Icc (0 : ℝ) 1
  have h2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  obtain ⟨K, hKc, hK, hKf⟩ := exists_isClosed_continuousOn_of_measurable hf.measurable_mk h2
  have hN : volume ({x | f x ≠ hf.mk f x} ∩ I) = 0 := by
    have := ae_iff.1 hf.ae_eq_mk
    rwa [Measure.restrict_apply' measurableSet_Icc] at this
  obtain ⟨U, hNU, hUo, hU⟩ :=
    Set.exists_isOpen_lt_of_lt _ (ε / 2) (by rw [hN]; exact pos_iff_ne_zero.2 h2)
  refine ⟨K ∩ Uᶜ ∩ I, inter_subset_right, (hKc.inter hUo.isClosed_compl).inter isClosed_Icc,
    ?_, ?_⟩
  · calc volume (I \ (K ∩ Uᶜ ∩ I)) ≤ volume ((I \ K) ∪ U) := by
          refine measure_mono fun x hx => ?_
          by_cases hxK : x ∈ K
          · by_cases hxU : x ∈ U
            · exact Or.inr hxU
            · exact absurd ⟨⟨hxK, hxU⟩, hx.1⟩ hx.2
          · exact Or.inl ⟨hx.1, hxK⟩
      _ ≤ volume (I \ K) + volume U := measure_union_le _ _
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hK hU
      _ = ε := ENNReal.add_halves _
  · refine (hKf.mono (inter_subset_left.trans inter_subset_left)).congr fun x hx => ?_
    by_contra h
    exact hx.1.2 (hNU ⟨h, hx.2⟩)

/-- Passing from "the complement has small measure" to Luzin's "the measure exceeds `1 - ε`". -/
lemma ofReal_one_sub_lt {P : Set ℝ} (hPI : P ⊆ Icc (0 : ℝ) 1) (hPm : MeasurableSet P) {ε : ℝ}
    (h : volume (Icc (0 : ℝ) 1 \ P) < ENNReal.ofReal (min ε 1)) :
    ENNReal.ofReal (1 - ε) < volume P := by
  have hfin : volume P ≠ ∞ := (measure_mono hPI |>.trans_lt measure_Icc_lt_top).ne
  rw [measure_sdiff hPI hPm.nullMeasurableSet hfin, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one] at h
  have hmin : 0 ≤ min ε 1 := (ENNReal.ofReal_pos.1 (lt_of_le_of_lt zero_le h)).le
  calc ENNReal.ofReal (1 - ε) ≤ ENNReal.ofReal (1 - min ε 1) :=
        ENNReal.ofReal_le_ofReal (by linarith [min_le_left ε 1])
    _ = 1 - ENNReal.ofReal (min ε 1) := by rw [ENNReal.ofReal_sub _ hmin, ENNReal.ofReal_one]
    _ < volume P := ENNReal.sub_lt_of_sub_lt (ENNReal.ofReal_le_one.2 (min_le_right _ _))
        (Or.inl ENNReal.one_ne_top) h

/-- Conversely, Luzin's "the measure exceeds `1 - ε`" bounds the measure of the complement. -/
lemma measure_sdiff_le_of_lt {P : Set ℝ} (hPI : P ⊆ Icc (0 : ℝ) 1) (hPm : MeasurableSet P)
    {ε : ℝ} (h : ENNReal.ofReal (1 - ε) < volume P) :
    volume (Icc (0 : ℝ) 1 \ P) ≤ ENNReal.ofReal ε := by
  have hfin : volume P ≠ ∞ := (measure_mono hPI |>.trans_lt measure_Icc_lt_top).ne
  rw [measure_sdiff hPI hPm.nullMeasurableSet hfin, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one, tsub_le_iff_right]
  calc (1 : ℝ≥0∞) = ENNReal.ofReal (ε + (1 - ε)) := by rw [add_sub_cancel, ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal (1 - ε) := ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal ε + volume P := add_le_add le_rfl h.le

/-- **Luzin's general theorem.** If `f` is a measurable function on `0 ≤ x ≤ 1`, then for every
`ε > 0` there is a perfect, nowhere dense set `P ⊆ [0, 1]` such that 1° `f` is continuous on `P`
(relatively to `P`) and 2° the measure of `P` exceeds `1 - ε`. -/
theorem cProperty_of_aemeasurable {f : ℝ → ℝ}
    (hf : AEMeasurable f (volume.restrict (Icc (0 : ℝ) 1))) : CProperty f := by
  intro ε hε
  set I := Icc (0 : ℝ) 1
  set η := ENNReal.ofReal (min ε 1)
  have hη : η ≠ 0 := (ENNReal.ofReal_pos.2 (lt_min hε one_pos)).ne'
  have h2 : η / 2 ≠ 0 := (ENNReal.half_pos hη).ne'
  obtain ⟨K, hKI, hKc, hK, hKf⟩ := exists_isClosed_continuousOn hf h2
  -- small balls around the rationals
  obtain ⟨r, rpos, hr⟩ := ENNReal.exists_pos_sum_of_countable h2 ℚ
  set U := ⋃ q : ℚ, ball (q : ℝ) ((r q : ℝ) / 2)
  have hUo : IsOpen U := isOpen_iUnion fun q => isOpen_ball
  have hU : volume U < η / 2 := by
    calc volume U ≤ ∑' q : ℚ, volume (ball (q : ℝ) ((r q : ℝ) / 2)) := measure_iUnion_le _
      _ = ∑' q : ℚ, (r q : ℝ≥0∞) := by
          congr 1; ext q
          rw [Real.volume_ball, mul_div_cancel₀ _ two_ne_zero, ENNReal.ofReal_coe_nnreal]
      _ < η / 2 := hr
  set L := K ∩ Uᶜ
  have hLc : IsClosed L := hKc.inter hUo.isClosed_compl
  have hLint : interior L = ∅ := by
    by_contra hne
    obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open isOpen_interior
      (nonempty_iff_ne_empty.2 hne)
    have hqU : (q : ℝ) ∈ U := mem_iUnion.2 ⟨q, mem_ball_self (half_pos (rpos q))⟩
    exact (interior_subset hq).2 hqU
  obtain ⟨V, D, hV, hD, hLVD⟩ := exists_countable_union_perfect_of_isClosed hLc
  have hDL : D ⊆ L := hLVD ▸ subset_union_right
  refine ⟨D, hDL.trans (inter_subset_left.trans hKI), hD,
    hD.closed.isNowhereDense_iff.2 (subset_empty_iff.1 (hLint ▸ interior_mono hDL)),
    hKf.mono (hDL.trans inter_subset_left), ofReal_one_sub_lt
      (hDL.trans (inter_subset_left.trans hKI)) hD.closed.measurableSet ?_⟩
  calc volume (I \ D) ≤ volume ((I \ K) ∪ U ∪ V) := by
        refine measure_mono fun x hx => ?_
        by_cases hxK : x ∈ K
        · by_cases hxU : x ∈ U
          · exact Or.inl (Or.inr hxU)
          · have hxL : x ∈ V ∪ D := hLVD ▸ ⟨hxK, hxU⟩
            rcases hxL with hxV | hxD
            · exact Or.inr hxV
            · exact absurd hxD hx.2
        · exact Or.inl (Or.inl ⟨hx.1, hxK⟩)
    _ ≤ volume (I \ K) + volume U + volume V :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ < η / 2 + η / 2 + 0 := by
        rw [hV.measure_zero, add_zero, add_zero]; exact ENNReal.add_lt_add hK hU
    _ = η := by rw [add_zero, ENNReal.add_halves]

/-- **Converse of Luzin's general theorem.** A function with the C-property is measurable on
`0 ≤ x ≤ 1`. -/
theorem aemeasurable_of_cProperty {f : ℝ → ℝ} (h : CProperty f) :
    AEMeasurable f (volume.restrict (Icc (0 : ℝ) 1)) := by
  set I := Icc (0 : ℝ) 1
  choose P hPI hPp _ hPf hPm using fun n : ℕ => h (1 / ((n : ℝ) + 1)) (by positivity)
  have hb : ∀ n : ℕ, volume (I \ ⋃ k, P k) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    (measure_mono (sdiff_subset_sdiff_right (subset_iUnion P n))).trans
      (measure_sdiff_le_of_lt (hPI n) (hPp n).closed.measurableSet (hPm n))
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [ENNReal.ofReal_zero] at this
  have h0 : volume (I \ ⋃ k, P k) = 0 := le_antisymm (ge_of_tendsto' ht hb) zero_le
  have hIS : volume.restrict I = volume.restrict (⋃ k, P k) := by
    refine Measure.restrict_congr_set (ae_eq_set.2 ⟨h0, ?_⟩)
    rw [sdiff_eq_empty.2 (iUnion_subset hPI), measure_empty]
  rw [hIS, aemeasurable_iUnion_iff]
  exact fun n => ContinuousOn.aemeasurable (hPf n) (hPp n).closed.measurableSet

/-- Luzin's theorem and its converse: on `0 ≤ x ≤ 1`, a function is measurable if and only if it
has the C-property. -/
theorem aemeasurable_iff_cProperty {f : ℝ → ℝ} :
    AEMeasurable f (volume.restrict (Icc (0 : ℝ) 1)) ↔ CProperty f :=
  ⟨cProperty_of_aemeasurable, aemeasurable_of_cProperty⟩

/-- **Luzin's theorem on limits.** If every function of the sequence `f₁, f₂, …` has the
C-property and the sequence converges to `f(x)` at every point of `0 ≤ x ≤ 1` outside a set of
measure zero, then the limit function `f` has the C-property. -/
theorem cProperty_of_tendsto {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (hfs : ∀ n, CProperty (fs n))
    (hlim : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
      Tendsto (fun n => fs n x) atTop (𝓝 (f x))) : CProperty f :=
  cProperty_of_aemeasurable
    (aemeasurable_of_tendsto_metrizable_ae' (fun n => aemeasurable_of_cProperty (hfs n)) hlim)

/-- **Luzin's theorem, modern form** (not stated in the note in this form). A measurable function
on `[0, 1]` agrees with a continuous function on `ℝ` outside a subset of `[0, 1]` of measure
less than `ε`. -/
theorem exists_continuous_eq_off {f : ℝ → ℝ}
    (hf : AEMeasurable f (volume.restrict (Icc (0 : ℝ) 1))) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : C(ℝ, ℝ), volume {x ∈ Icc (0 : ℝ) 1 | f x ≠ g x} < ε := by
  obtain ⟨K, -, hKc, hK, hKf⟩ := exists_isClosed_continuousOn hf hε
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hKc
    (⟨K.domRestrict f, continuousOn_iff_continuous_domRestrict.1 hKf⟩ : C(K, ℝ))
  have hsub : {x ∈ Icc (0 : ℝ) 1 | f x ≠ g x} ⊆ Icc (0 : ℝ) 1 \ K := by
    intro x hx
    refine ⟨hx.1, fun hxK => hx.2 ?_⟩
    have := congrArg (fun φ : C(K, ℝ) => φ ⟨x, hxK⟩) hg
    simpa using this.symm
  exact ⟨g, (measure_mono hsub).trans_lt hK⟩

/-- **Consequence in the note.** If `f` is a measurable function on `0 ≤ x ≤ 1`, there is a series
of polynomials `∑ pₙ(x)` converging absolutely to `f(x)` at every point of `0 ≤ x ≤ 1` outside
a set of measure zero. ("Absolutely convergent" is `Summable fun n ↦ |pₙ(x)|`; the sum is `f(x)`
by `HasSum`.) -/
theorem exists_polynomial_series {f : ℝ → ℝ}
    (hf : AEMeasurable f (volume.restrict (Icc (0 : ℝ) 1))) :
    ∃ p : ℕ → Polynomial ℝ, ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
      Summable (fun n => |(p n).eval x|) ∧ HasSum (fun n => (p n).eval x) (f x) := by
  set I := Icc (0 : ℝ) 1
  -- continuous `gₙ` agreeing with `f` off a set of measure `< 2⁻ⁿ`
  choose g hg using fun n : ℕ =>
    exists_continuous_eq_off hf (ε := (2⁻¹ : ℝ≥0∞) ^ n) (by simp)
  -- polynomials `qₙ` within `(1/2)ⁿ` of `gₙ` on `[0, 1]` (Weierstrass)
  have hw : ∀ n : ℕ, ∃ q : Polynomial ℝ, ∀ x ∈ I, |q.eval x - g n x| < (1 / 2 : ℝ) ^ n := by
    intro n
    obtain ⟨q, hq⟩ :=
      exists_polynomial_near_continuousMap 0 1 ((g n).restrict I) ((1 / 2 : ℝ) ^ n) (by positivity)
    refine ⟨q, fun x hx => ?_⟩
    have := (ContinuousMap.norm_coe_le_norm
      (q.toContinuousMapOn I - (g n).restrict I) ⟨x, hx⟩).trans_lt hq
    simpa [Real.norm_eq_abs] using this
  choose q hq using hw
  -- telescoping series `p₀ = q₀`, `pₙ = qₙ - qₙ₋₁`
  set p : ℕ → Polynomial ℝ := fun n => q n - if n = 0 then 0 else q (n - 1) with hp
  have htele : ∀ x n, ∑ k ∈ Finset.range (n + 1), (p k).eval x = (q n).eval x := by
    intro x n
    induction n with
    | zero => simp [hp]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [hp]
  refine ⟨p, ?_⟩
  -- Borel–Cantelli: a.e. `x` lies in only finitely many of the sets `{f ≠ gₙ}`
  have hsum : ∑' n, volume.restrict I {x | f x ≠ g n x} ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n) ?_
      (ENNReal.tsum_le_tsum fun n => ?_)
    · rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.ofNat_ne_top
    · rw [Measure.restrict_apply' measurableSet_Icc]
      have hsub : {x | f x ≠ g n x} ∩ I ⊆ {x ∈ I | f x ≠ g n x} := fun x hx => ⟨hx.2, hx.1⟩
      exact (measure_mono hsub).trans (hg n).le
  filter_upwards [ae_eventually_notMem hsum, ae_restrict_mem measurableSet_Icc] with x hx hxI
  have hQf : ∀ᶠ n in atTop, |(q n).eval x - f x| < (1 / 2 : ℝ) ^ n := by
    filter_upwards [hx] with n hn
    have : f x = g n x := by simpa using hn
    rw [this]; exact hq n x hxI
  have hQ : Tendsto (fun n => (q n).eval x) atTop (𝓝 (f x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
    filter_upwards [hQf] with n hn
    rw [Real.norm_eq_abs]; exact hn.le
  obtain ⟨N, hN⟩ := eventually_atTop.1 hQf
  have habs : Summable (fun n => |(p n).eval x|) := by
    refine Summable.of_norm_bounded_eventually (summable_geometric_two.mul_left 4) ?_
    rw [Nat.cofinite_eq_atTop]
    refine eventually_atTop.2 ⟨N + 1, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 := hN (m + 1) (by omega)
    have h2 := hN m (by omega)
    have hpm : (p (m + 1)).eval x = (q (m + 1)).eval x - (q m).eval x := by simp [hp]
    rw [Real.norm_eq_abs, abs_abs, hpm]
    calc |(q (m + 1)).eval x - (q m).eval x|
        ≤ |(q (m + 1)).eval x - f x| + |f x - (q m).eval x| := abs_sub_le _ _ _
      _ = |(q (m + 1)).eval x - f x| + |(q m).eval x - f x| := by rw [abs_sub_comm (f x)]
      _ ≤ (1 / 2 : ℝ) ^ (m + 1) + (1 / 2 : ℝ) ^ m := add_le_add h1.le h2.le
      _ ≤ 4 * (1 / 2 : ℝ) ^ (m + 1) := by
          rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m]
  have hs : Summable (fun n => (p n).eval x) :=
    Summable.of_norm (by simpa [Real.norm_eq_abs] using habs)
  refine ⟨habs, ?_⟩
  have h1 : Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), (p k).eval x) atTop
      (𝓝 (∑' n, (p n).eval x)) :=
    hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), (p k).eval x) atTop (𝓝 (f x)) := by
    simpa only [htele] using hQ
  rw [← tendsto_nhds_unique h1 h2]
  exact hs.hasSum

end SovietLean.Luzin1912
