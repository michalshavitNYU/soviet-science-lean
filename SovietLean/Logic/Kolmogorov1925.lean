module

public import Mathlib.Data.Set.Image

/-!
# Kolmogorov (1925), *On the principle of tertium non datur*

Entry: `entries/logic/1925-kolmogorov-tertium-non-datur/`.

Original: А. Н. Колмогоров, «О принципе tertium non datur», Матем. сб. 32:4 (1925), 646–667.

**The paper.** Kolmogorov writes the logic of judgements with implication `A → B` and negation
`Ā` only (no conjunction, disjunction or falsum). Chapter II sets up two Hilbert-style systems,
both with the rules of substitution and modus ponens (`𝔖, 𝔖 → 𝔗 | 𝔗`):

* the four axioms of implication (1), taken from Hilbert:
  1. `A → (B → A)`,
  2. `{A → (A → B)} → (A → B)`,
  3. `{A → (B → C)} → {B → (A → C)}`,
  4. `(B → C) → {(A → B) → (A → C)}`;
* his own "principle of contradiction" (3), numbered axiom 5:
  `(A → B) → {(A → B̄) → Ā}`;
* the axiom of double negation (4), numbered axiom 6: `Ā̄ → A`.

Axioms 1–5 form the system `𝔅`, the *general* logic of judgements, valid for every judgement
(today: minimal propositional logic with a primitive negation). Adding axiom 6 gives `ℌ`,
the *special* logic of judgements; Kolmogorov shows in ch. II § 8 that
`ℌ` is equivalent to Hilbert's classical system, deriving Hilbert's axioms
`A → (Ā → B)` as his formula (18) and `(A → B) → {(Ā → B) → B}` as (26).

Chapter IV builds "pseudomathematics": to each formula `𝔖` it assigns `𝔖*`, where for an
elementary formula `𝔖* = n𝔖` (48), `n` meaning double negation, and for a compound formula
`F(𝔖₁, …, 𝔖ₖ)* = n F(𝔖₁*, …, 𝔖ₖ*)` (49). For the two connectives this reads
`(A → B)* = n(A* → B*)` and `(Ā)* = n(\overline{A*})`, as in his list (54). The main theorem
(ch. IV §§ 3–6): whatever is provable from axioms `𝔘` with the help of double negation (4) has
its `*`-translation provable from the translated axioms `𝔘*` without (4); so classical
conclusions are intuitionistically valid when every judgement is read as its "pseudotruth"
(double negation). Along the way: every negation is "of type `A·`", i.e. stable under double
negation (36): `Ā̄̄ → Ā`; and stability is preserved by implication (46)–(47).

**Formal version.**

* `Formula`: propositional formulas built from variables by `⇒` (Kolmogorov's `→`) and `∼`
  (his bar).
* `Proves S Γ A`: `A` is derivable in the system `S = .B` (axioms 1–5, Kolmogorov's `𝔅`) or
  `S = .H` (axioms 1–6, his `ℌ`) from the extra hypotheses `Γ`, with modus ponens.
  The axioms are stated as schemes, which replaces the paper's rule of substitution.
  The hypotheses `Γ` play the role of the paper's mathematical axioms `𝔘₁, …, 𝔘ₖ`; with
  `Γ = ∅` one gets the pure logic of judgements.
* `kol`: the translation `*` of (48)–(49), applied to every subformula.
* `kolmogorov`: if `Γ ⊢ A` in `ℌ` then `Γ* ⊢ A*` in `𝔅` (ch. IV § 3–§ 6, the paper's main
  theorem, propositional part). `kolmogorov_converse` and `kolmogorov_iff` add the converse
  (not stated in the paper, but immediate from the equivalence `A ↔ A*` in `ℌ`,
  `kol_equiv_H`).
  Kolmogorov checks the translated axioms (54) by proving the formulas (55) in the special
  logic, which he has shown to be valid for judgements of type `A·` (ch. III § 4); here they
  are derived directly in `𝔅`.
* `stable_kol`: `𝔅 ⊢ n(A*) → A*`, i.e. every translated formula is "of type `A·`"
  (ch. III § 3 and ch. IV § 2).
* Kolmogorov's numbered formulas proved in `𝔅`: (10), (12), (24), (34), (36), (46); and in `ℌ`
  Hilbert's axioms (18), (26). The derivations are ours (by way of a deduction theorem,
  `deduction`), not his line-by-line chains of substitutions.
* `not_B_dne`, `not_B_efq`: axiom 6 and Hilbert's axiom `A → (Ā → B)` are *not* provable in
  `𝔅`. The paper leaves the first only implicit (the underlining of formulas that need axiom 6)
  and explicitly does not exclude the second (ch. II § 4); these are modern additions, proved
  with the two-valued model in which every negation is true.

**Not formalized.** The quantifier part of ch. V (axioms I–IV (63), formulas (59)–(62)); the
paper's claim that all known axioms of mathematics are "of type `𝔎`" (their translations are
true); the applications to real numbers and transfinite induction (ch. V §§ 5–6).
-/

@[expose] public section

namespace SovietLean.Kolmogorov1925

/-- Formulas of Kolmogorov's logic of judgements: variables `A, B, C, …`, implication `A → B`
and negation `Ā`. -/
inductive Formula : Type
  | var : ℕ → Formula
  | imp : Formula → Formula → Formula
  | neg : Formula → Formula
  deriving DecidableEq

@[inherit_doc] scoped infixr:25 " ⇒ " => Formula.imp
@[inherit_doc] scoped prefix:max "∼" => Formula.neg

open Formula

/-- The two systems of ch. II: `B` is Kolmogorov's `𝔅` (axioms 1–5, the general logic of
judgements); `H` is his `ℌ` (axioms 1–6, the special logic of judgements). -/
inductive System : Type
  | B
  | H
  deriving DecidableEq

/-- `Proves S Γ A`: `A` is derivable in the system `S` from the hypotheses `Γ`.
The axioms are Kolmogorov's 1–6 (ch. II, (1), (3), (4)), as schemes; the only rule is modus
ponens. Axiom 6 (double negation) is available only in `ℌ = H`. -/
inductive Proves (S : System) (Γ : Set Formula) : Formula → Prop
  | hyp {A : Formula} : A ∈ Γ → Proves S Γ A
  /-- Axiom 1: `A → (B → A)`. -/
  | ax1 (A B : Formula) : Proves S Γ (A ⇒ (B ⇒ A))
  /-- Axiom 2: `{A → (A → B)} → (A → B)`. -/
  | ax2 (A B : Formula) : Proves S Γ ((A ⇒ (A ⇒ B)) ⇒ (A ⇒ B))
  /-- Axiom 3: `{A → (B → C)} → {B → (A → C)}`. -/
  | ax3 (A B C : Formula) : Proves S Γ ((A ⇒ (B ⇒ C)) ⇒ (B ⇒ (A ⇒ C)))
  /-- Axiom 4: `(B → C) → {(A → B) → (A → C)}`. -/
  | ax4 (A B C : Formula) : Proves S Γ ((B ⇒ C) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
  /-- Axiom 5, Kolmogorov's principle of contradiction (3): `(A → B) → {(A → B̄) → Ā}`. -/
  | ax5 (A B : Formula) : Proves S Γ ((A ⇒ B) ⇒ ((A ⇒ ∼B) ⇒ ∼A))
  /-- Axiom 6, double negation (4): `Ā̄ → A`; only in `ℌ`. -/
  | ax6 (A : Formula) : S = .H → Proves S Γ (∼∼A ⇒ A)
  /-- Modus ponens, the scheme `𝔖, 𝔖 → 𝔗 | 𝔗`. -/
  | mp {A B : Formula} : Proves S Γ (A ⇒ B) → Proves S Γ A → Proves S Γ B

/-- Kolmogorov's translation into "pseudomathematics", (48)–(49): put a double negation `n`
in front of every subformula. `(A → B)* = n(A* → B*)`, `(Ā)* = n(\overline{A*})`. -/
def kol : Formula → Formula
  | var p => ∼∼(var p)
  | imp A B => ∼∼(kol A ⇒ kol B)
  | neg A => ∼∼∼(kol A)

namespace Proves

variable {S : System} {Γ Δ : Set Formula} {A B C : Formula}

/-- Cut: hypotheses that are themselves derivable can be discharged. -/
theorem cut (hΓ : ∀ B ∈ Γ, Proves S Δ B) (h : Proves S Γ A) : Proves S Δ A := by
  induction h with
  | hyp hA => exact hΓ _ hA
  | ax1 => exact .ax1 _ _
  | ax2 => exact .ax2 _ _
  | ax3 => exact .ax3 _ _ _
  | ax4 => exact .ax4 _ _ _
  | ax5 => exact .ax5 _ _
  | ax6 A hS => exact .ax6 A hS
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

theorem weaken (hΓΔ : Γ ⊆ Δ) (h : Proves S Γ A) : Proves S Δ A :=
  cut (fun _ hB => .hyp (hΓΔ hB)) h

theorem weaken_insert (h : Proves S Γ A) : Proves S (insert B Γ) A :=
  weaken (Set.subset_insert _ _) h

/-- What `𝔅` proves, `ℌ` proves. -/
theorem B_to (h : Proves .B Γ A) : Proves S Γ A := by
  induction h with
  | hyp hA => exact .hyp hA
  | ax1 => exact .ax1 _ _
  | ax2 => exact .ax2 _ _
  | ax3 => exact .ax3 _ _ _
  | ax4 => exact .ax4 _ _ _
  | ax5 => exact .ax5 _ _
  | ax6 _ hS => exact absurd hS (by decide)
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

/-- Formula (27): `A → A`, from axioms 1 and 2. -/
theorem imp_self : Proves S Γ (A ⇒ A) :=
  .mp (.ax2 A A) (.ax1 A A)

/-- From `A → (C → B)` and `A → C`, infer `A → B` (axioms 2–4). -/
theorem imp_mp (h₁ : Proves S Γ (A ⇒ (C ⇒ B))) (h₂ : Proves S Γ (A ⇒ C)) :
    Proves S Γ (A ⇒ B) := by
  have t₁ : Proves S Γ ((A ⇒ (C ⇒ B)) ⇒ (A ⇒ ((A ⇒ C) ⇒ (A ⇒ B)))) :=
    .mp (.ax4 A (C ⇒ B) ((A ⇒ C) ⇒ (A ⇒ B))) (.ax4 A C B)
  have t₂ := Proves.mp t₁ h₁
  have t₃ : Proves S Γ ((A ⇒ C) ⇒ (A ⇒ (A ⇒ B))) := .mp (.ax3 A (A ⇒ C) (A ⇒ B)) t₂
  exact .mp (.ax2 A B) (.mp t₃ h₂)

/-- The deduction theorem for axioms 1–4 with modus ponens. -/
theorem deduction (h : Proves S (insert A Γ) B) : Proves S Γ (A ⇒ B) := by
  induction h with
  | hyp hB =>
    rcases Set.mem_insert_iff.mp hB with rfl | hB
    · exact imp_self
    · exact .mp (.ax1 _ _) (.hyp hB)
  | ax1 => exact .mp (.ax1 _ _) (.ax1 _ _)
  | ax2 => exact .mp (.ax1 _ _) (.ax2 _ _)
  | ax3 => exact .mp (.ax1 _ _) (.ax3 _ _ _)
  | ax4 => exact .mp (.ax1 _ _) (.ax4 _ _ _)
  | ax5 => exact .mp (.ax1 _ _) (.ax5 _ _)
  | ax6 C hS => exact .mp (.ax1 _ _) (.ax6 C hS)
  | mp _ _ ih₁ ih₂ => exact imp_mp ih₁ ih₂

/-- Negation introduction, from axiom 5: if `A` yields both `B` and `B̄`, then `Ā`. -/
theorem neg_intro (h₁ : Proves S (insert A Γ) B) (h₂ : Proves S (insert A Γ) (∼B)) :
    Proves S Γ (∼A) :=
  .mp (.mp (.ax5 A B) (deduction h₁)) (deduction h₂)

/-- `A ⊢ Ā̄`, the rule form of (34). -/
theorem dni (h : Proves S Γ A) : Proves S Γ (∼∼A) :=
  neg_intro (B := A) (weaken_insert h) (.hyp (Set.mem_insert _ _))

/-- From `A` and `Ā`, any negation follows. -/
theorem absurd_neg (h₁ : Proves S Γ A) (h₂ : Proves S Γ (∼A)) : Proves S Γ (∼C) :=
  neg_intro (B := A) (weaken_insert h₁) (weaken_insert h₂)

/-- `Ā̄̄ ⊢ Ā`, the rule form of Brouwer's formula (36). -/
theorem tne (h : Proves S Γ (∼∼∼A)) : Proves S Γ (∼A) :=
  neg_intro (B := ∼∼A) (dni (.hyp (Set.mem_insert _ _))) (weaken_insert h)

/-- Modus ponens under double negation: from `n(A → B)` and `A`, infer `nB`. -/
theorem mp_dn (h : Proves S Γ (∼∼(A ⇒ B))) (hA : Proves S Γ A) : Proves S Γ (∼∼B) := by
  refine neg_intro (B := ∼(A ⇒ B)) ?_ (weaken_insert h)
  refine neg_intro (B := B) ?_ (weaken_insert (.hyp (Set.mem_insert _ _)))
  exact .mp (.hyp (Set.mem_insert _ _)) (weaken_insert (weaken_insert hA))

end Proves

open Proves

variable {Γ : Set Formula} {A B C : Formula}

/-! ### Kolmogorov's numbered formulas -/

/-- Formula (34): `A → Ā̄`, in `𝔅`. -/
theorem f34 : Proves .B Γ (A ⇒ ∼∼A) :=
  deduction (dni (.hyp (Set.mem_insert _ _)))

/-- Formula (36), Brouwer: `Ā̄̄ → Ā`, in `𝔅`. Every negation is "of type `A·`". -/
theorem f36 : Proves .B Γ (∼∼∼A ⇒ ∼A) :=
  deduction (tne (.hyp (Set.mem_insert _ _)))

/-- Formula (10), contraposition: `(A → B) → (B̄ → Ā)`, in `𝔅`. -/
theorem f10 : Proves .B Γ ((A ⇒ B) ⇒ (∼B ⇒ ∼A)) := by
  refine deduction (deduction ?_)
  refine neg_intro (B := B) ?_ (weaken_insert (.hyp (Set.mem_insert _ _)))
  exact .mp (.hyp (by simp)) (.hyp (Set.mem_insert _ _))

/-- Formula (12): `A → (Ā → B̄)`, in `𝔅`. -/
theorem f12 : Proves .B Γ (A ⇒ (∼A ⇒ ∼B)) :=
  deduction (deduction (absurd_neg (.hyp (by simp)) (.hyp (Set.mem_insert _ _))))

/-- Formula (24): `(A → B) → {(Ā → B) → B̄̄}`, in `𝔅`: if `B` follows both from `A` and from
`Ā`, then `B` cannot be false. -/
theorem f24 : Proves .B Γ ((A ⇒ B) ⇒ ((∼A ⇒ B) ⇒ ∼∼B)) := by
  refine deduction (deduction ?_)
  refine neg_intro (B := B) ?_ (.hyp (Set.mem_insert _ _))
  -- context: `B̄`, `Ā → B`, `A → B`, Γ
  have hnA : Proves .B (insert (∼B) (insert (∼A ⇒ B) (insert (A ⇒ B) Γ))) (∼A) := by
    refine neg_intro (B := B) ?_ (weaken_insert (.hyp (Set.mem_insert _ _)))
    exact .mp (.hyp (by simp)) (.hyp (Set.mem_insert _ _))
  exact .mp (.hyp (by simp)) hnA

/-- Formula (46): `n(A → B) → (A → nB)`, in `𝔅`. -/
theorem f46 : Proves .B Γ (∼∼(A ⇒ B) ⇒ (A ⇒ ∼∼B)) :=
  deduction (deduction (mp_dn (.hyp (by simp)) (.hyp (Set.mem_insert _ _))))

/-- Formula (18), Hilbert's first axiom of negation: `A → (Ā → B)`, in `ℌ`. -/
theorem f18 : Proves .H Γ (A ⇒ (∼A ⇒ B)) := by
  refine deduction (deduction ?_)
  refine .mp (.ax6 B rfl) ?_
  exact absurd_neg (A := A) (.hyp (by simp)) (.hyp (by simp))

/-- Formula (26), Hilbert's second axiom of negation (tertium non datur):
`(A → B) → {(Ā → B) → B}`, in `ℌ`. -/
theorem f26 : Proves .H Γ ((A ⇒ B) ⇒ ((∼A ⇒ B) ⇒ B)) := by
  refine deduction (deduction ?_)
  refine .mp (.ax6 B rfl) ?_
  exact .mp (.mp (B_to f24) (.hyp (by simp))) (.hyp (Set.mem_insert _ _))

/-! ### The translation -/

/-- Every translated formula is a negation. -/
theorem kol_neg (A : Formula) : ∃ X, kol A = ∼X := by
  cases A <;> exact ⟨_, rfl⟩

/-- Every translated formula is "of type `A·`" (ch. III § 3, ch. IV § 2): from `n(A*)` follows
`A*`, in `𝔅`. -/
theorem stable_kol (A : Formula) : Proves .B Γ (∼∼(kol A) ⇒ kol A) := by
  obtain ⟨X, hX⟩ := kol_neg A
  rw [hX]
  exact f36

theorem Proves.stable {Γ : Set Formula} {S : System} (h : Proves S Γ (∼∼(kol A))) :
    Proves S Γ (kol A) := by
  obtain ⟨X, hX⟩ := kol_neg A
  rw [hX] at h ⊢
  exact tne h

/-- The scheme (50): from `𝔖*` and `(𝔖 → 𝔗)*` infer `𝔗*`. -/
theorem Proves.mp_kol {Γ : Set Formula} {S : System} (h : Proves S Γ (kol (A ⇒ B)))
    (hA : Proves S Γ (kol A)) : Proves S Γ (kol B) :=
  Proves.stable (mp_dn h hA)

/-- Introduction of a translated implication. -/
theorem Proves.intro_kol {Γ : Set Formula} {S : System}
    (h : Proves S (insert (kol A) Γ) (kol B)) : Proves S Γ (kol (A ⇒ B)) :=
  dni (deduction h)

/-- **Kolmogorov's theorem** (ch. IV §§ 3–6, propositional part). If `A` is derivable in the
special (classical) logic `ℌ` from hypotheses `Γ`, then its translation `A*` is derivable in
the general logic `𝔅`, without double negation, from the translated hypotheses `Γ*`. -/
theorem kolmogorov (h : Proves .H Γ A) : Proves .B (kol '' Γ) (kol A) := by
  induction h with
  | hyp hA => exact .hyp (Set.mem_image_of_mem _ hA)
  | ax1 A B =>
    exact Proves.intro_kol (Proves.intro_kol (.hyp (by simp)))
  | ax2 A B =>
    refine Proves.intro_kol (Proves.intro_kol ?_)
    exact Proves.mp_kol (Proves.mp_kol (.hyp (by simp)) (.hyp (Set.mem_insert _ _)))
      (.hyp (Set.mem_insert _ _))
  | ax3 A B C =>
    refine Proves.intro_kol (Proves.intro_kol (Proves.intro_kol ?_))
    exact Proves.mp_kol (A := B) (B := C)
      (Proves.mp_kol (A := A) (B := B ⇒ C) (.hyp (by simp)) (.hyp (Set.mem_insert _ _)))
      (.hyp (by simp))
  | ax4 A B C =>
    refine Proves.intro_kol (Proves.intro_kol (Proves.intro_kol ?_))
    exact Proves.mp_kol (A := B) (B := C) (.hyp (by simp))
      (Proves.mp_kol (A := A) (B := B) (.hyp (by simp)) (.hyp (Set.mem_insert _ _)))
  | ax5 A B =>
    refine Proves.intro_kol (Proves.intro_kol ?_)
    refine dni (neg_intro (B := kol B) ?_ ?_)
    · exact Proves.mp_kol (.hyp (by simp)) (.hyp (Set.mem_insert _ _))
    · exact tne (Proves.mp_kol (B := ∼B) (.hyp (by simp)) (.hyp (Set.mem_insert _ _)))
  | ax6 A _ =>
    refine Proves.intro_kol ?_
    have h : Proves .B (insert (kol (∼∼A)) (kol '' Γ)) (∼∼∼(∼∼∼(kol A))) :=
      .hyp (Set.mem_insert _ _)
    exact Proves.stable (tne (A := ∼(kol A)) (tne h))
  | mp _ _ ih₁ ih₂ => exact Proves.mp_kol ih₁ ih₂

/-- In `ℌ`, every formula is equivalent to its translation. -/
theorem kol_equiv_H (A : Formula) :
    Proves .H ∅ (kol A ⇒ A) ∧ Proves .H ∅ (A ⇒ kol A) := by
  induction A with
  | var p =>
    exact ⟨.ax6 _ rfl, deduction (dni (.hyp (Set.mem_insert _ _)))⟩
  | imp A B ihA ihB =>
    refine ⟨deduction (deduction ?_), deduction (dni (deduction ?_))⟩
    · -- context: `A`, `n(A* → B*)`
      have hA' : Proves .H (insert A (insert (kol (A ⇒ B)) ∅)) (kol A) :=
        .mp (weaken (Set.empty_subset _) ihA.2) (.hyp (Set.mem_insert _ _))
      have hAB : Proves .H (insert A (insert (kol (A ⇒ B)) ∅)) (kol A ⇒ kol B) :=
        .mp (.ax6 _ rfl) (.hyp (by simp [kol]))
      exact .mp (weaken (Set.empty_subset _) ihB.1) (.mp hAB hA')
    · -- context: `A*`, `A → B`
      have hA : Proves .H (insert (kol A) (insert (A ⇒ B) ∅)) A :=
        .mp (weaken (Set.empty_subset _) ihA.1) (.hyp (Set.mem_insert _ _))
      exact .mp (weaken (Set.empty_subset _) ihB.2) (.mp (.hyp (by simp)) hA)
  | neg A ihA =>
    refine ⟨deduction ?_, deduction (dni ?_)⟩
    · -- context: `n(\overline{A*})`
      refine neg_intro (B := kol A) ?_ (weaken_insert (tne (.hyp (Set.mem_insert _ _))))
      exact .mp (weaken (Set.empty_subset _) ihA.2) (.hyp (Set.mem_insert _ _))
    · -- context: `Ā`
      refine neg_intro (B := A) ?_ (weaken_insert (.hyp (Set.mem_insert _ _)))
      exact .mp (weaken (Set.empty_subset _) ihA.1) (.hyp (Set.mem_insert _ _))

/-- Converse of `kolmogorov` (not in the paper): if `Γ* ⊢ A*` in `𝔅`, then `Γ ⊢ A` in `ℌ`. -/
theorem kolmogorov_converse (h : Proves .B (kol '' Γ) (kol A)) : Proves .H Γ A := by
  have h' : Proves .H Γ (kol A) := by
    refine cut ?_ (B_to h)
    rintro _ ⟨γ, hγ, rfl⟩
    exact .mp (weaken (Set.empty_subset _) (kol_equiv_H γ).2) (.hyp hγ)
  exact .mp (weaken (Set.empty_subset _) (kol_equiv_H A).1) h'

/-- `Γ ⊢ A` classically iff `Γ* ⊢ A*` in Kolmogorov's general logic `𝔅`. -/
theorem kolmogorov_iff : Proves .H Γ A ↔ Proves .B (kol '' Γ) (kol A) :=
  ⟨kolmogorov, kolmogorov_converse⟩

/-! ### `𝔅` is strictly weaker than `ℌ` (modern addition) -/

/-- The two-valued model in which every negation is true. All axioms 1–5 hold in it. -/
def evalTriv (v : ℕ → Prop) : Formula → Prop
  | var p => v p
  | imp A B => evalTriv v A → evalTriv v B
  | neg _ => True

theorem sound_triv (v : ℕ → Prop) (h : Proves .B Γ A) (hΓ : ∀ γ ∈ Γ, evalTriv v γ) :
    evalTriv v A := by
  induction h with
  | hyp hA => exact hΓ _ hA
  | ax1 => exact fun a _ => a
  | ax2 => exact fun f a => f a a
  | ax3 => exact fun f b a => f a b
  | ax4 => exact fun g f a => g (f a)
  | ax5 => exact fun _ _ => trivial
  | ax6 _ hS => exact absurd hS (by decide)
  | mp _ _ ih₁ ih₂ => exact ih₁ ih₂

/-- Axiom 6, double negation `Ā̄ → A`, is not provable in `𝔅`. -/
theorem not_B_dne : ¬ Proves .B ∅ (∼∼(var 0) ⇒ var 0) := fun h =>
  sound_triv (fun _ => False) h (by simp) trivial

/-- Hilbert's first axiom of negation `A → (Ā → B)` (Kolmogorov's (18)) is not provable in `𝔅`. -/
theorem not_B_efq : ¬ Proves .B ∅ (var 0 ⇒ (∼(var 0) ⇒ var 1)) := fun h =>
  absurd (sound_triv (fun n => n = 0) h (by simp) rfl trivial) (by simp [evalTriv])

end SovietLean.Kolmogorov1925
