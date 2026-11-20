## Background

In the early 1920s Brouwer argued that the law of excluded middle ("tertium non datur": every
statement is true or false) is not justified for statements about infinite collections. Hilbert
answered by turning logic into a formal calculus and trying to prove it consistent. Kolmogorov,
then 22, wrote this paper in Moscow in 1925. He asks why mathematics that uses excluded middle
illegitimately has never run into a contradiction, and answers by showing that classical
reasoning can be read inside a weaker logic that does not use it. The paper was little known
outside Russia until van Heijenoort's English translation (1967). Gödel (1933) and Gentzen
(1933–36) later found similar "negative translations" independently.

## The two systems of logic

Kolmogorov works with judgements $A, B, C, \ldots$, implication $A \to B$ and negation, which he
writes as a bar, $\overline{A}$. He takes Hilbert's four axioms for implication:

1. $A \to (B \to A)$,
2. $\{A \to (A \to B)\} \to (A \to B)$,
3. $\{A \to (B \to C)\} \to \{B \to (A \to C)\}$,
4. $(B \to C) \to \{(A \to B) \to (A \to C)\}$.

Hilbert's two axioms for negation were $A \to (\overline{A} \to B)$ ("from a falsehood
everything follows") and $(A \to B) \to \{(\overline{A} \to B) \to B\}$ (excluded middle in the
form used in proofs). Kolmogorov rejects both as axioms for arbitrary judgements. In their place
he proposes his *principle of contradiction*:

5. $(A \to B) \to \{(A \to \overline{B}) \to \overline{A}\}$: if a statement implies both
   something and its negation, the statement is false.

Axioms 1–5 form the system $\mathfrak{B}$, the *general logic of judgements*, which he regards
as valid for every judgement. Today this is called minimal logic. Adding the axiom of double
negation

6. $\overline{\overline{A}} \to A$

gives the system $\mathfrak{H}$, the *special logic of judgements*. Kolmogorov shows that
$\mathfrak{H}$ proves both of Hilbert's negation axioms (his formulas (18) and (26)), so it is
classical logic. He accepts axiom 6 only for "finitary" judgements, and he notes that every
negative judgement $\overline{A}$ satisfies it already in $\mathfrak{B}$, by Brouwer's rule
$\overline{\overline{\overline{A}}} \to \overline{A}$ (36).

## The idea: read every statement as its double negation

Call a judgement *pseudotrue* when its double negation is true. Kolmogorov builds a
"pseudomathematics" by attaching a double negation $n$ to every part of every formula:
$$\mathfrak{S}^* = n\mathfrak{S} \text{ for an elementary formula}, \qquad
(A \to B)^* = n(A^* \to B^*), \qquad (\overline{A})^* = n(\overline{A^*}).$$

Why this works. Every translated formula starts with a negation, and negations behave
classically even in $\mathfrak{B}$: double negation can be removed from them. Kolmogorov then
checks two things. First, each axiom, after translation, is provable in $\mathfrak{B}$; this
includes axiom 6, because removing a double negation from a negation is allowed. Second, modus
ponens survives translation: from $A^*$ and $n(A^* \to B^*)$ one gets $nB^*$, and since $B^*$ is a
negation, $B^*$ itself (scheme (50)). A classical proof can therefore be copied line by line into a
proof in $\mathfrak{B}$ of the translated statements.

The conclusion (ch. IV § 6): every theorem of classical mathematics is correct when each
statement in it is read as an assertion of its pseudotruth. For finitary statements,
pseudotruth is ordinary truth, so finitary conclusions reached by transfinite use of excluded
middle are correct. And excluded middle can never lead to a contradiction, because the
contradiction would translate into one in $\mathfrak{B}$.

Chapter V extends the discussion to quantifiers ("for all $(a)$", "there is $(a)$"), proves
which of Hilbert's quantifier rules need double negation, and gives examples (decimal
expansions of reals, open complements of closed sets, transfinite induction) of results that
seem to need excluded middle.

## What the Lean file proves

The Lean file `SovietLean/Logic/Kolmogorov1925.lean` treats the propositional part. Formulas are
built from variables with `⇒` (implication) and `∼` (negation). `Proves S Γ A` says that $A$
follows from the hypotheses $\Gamma$ in system $S$ ($\mathfrak{B}$ or $\mathfrak{H}$), with
Kolmogorov's axioms 1–6 as schemes and modus ponens as the only rule. Nothing uses `sorry`.

| Paper | Lean | Status |
|---|---|---|
| Ch. IV §§ 3–6: if $\Gamma \vdash A$ in $\mathfrak{H}$ then $\Gamma^* \vdash A^*$ in $\mathfrak{B}$ | `kolmogorov` | proved |
| Converse: if $\Gamma^* \vdash A^*$ in $\mathfrak{B}$ then $\Gamma \vdash A$ in $\mathfrak{H}$ (not in the paper) | `kolmogorov_converse`, `kolmogorov_iff` | proved |
| $A^* \to A$ and $A \to A^*$ in $\mathfrak{H}$ | `kol_equiv_H` | proved |
| Ch. III § 3, IV § 2: $n(A^*) \to A^*$ in $\mathfrak{B}$ (translations are "of type $A^{\cdot}$") | `stable_kol` | proved |
| (50): from $\mathfrak{S}^*$ and $(\mathfrak{S} \to \mathfrak{T})^*$ infer $\mathfrak{T}^*$ | `Proves.mp_kol` | proved |
| (10): $(A \to B) \to (\overline{B} \to \overline{A})$ in $\mathfrak{B}$ | `f10` | proved |
| (12): $A \to (\overline{A} \to \overline{B})$ in $\mathfrak{B}$ | `f12` | proved |
| (24): $(A \to B) \to \{(\overline{A} \to B) \to \overline{\overline{B}}\}$ in $\mathfrak{B}$ | `f24` | proved |
| (34): $A \to \overline{\overline{A}}$ in $\mathfrak{B}$ | `f34` | proved |
| (36): $\overline{\overline{\overline{A}}} \to \overline{A}$ in $\mathfrak{B}$ | `f36` | proved |
| (46): $n(A \to B) \to (A \to nB)$ in $\mathfrak{B}$ | `f46` | proved |
| (18): $A \to (\overline{A} \to B)$ in $\mathfrak{H}$ | `f18` | proved |
| (26): $(A \to B) \to \{(\overline{A} \to B) \to B\}$ in $\mathfrak{H}$ | `f26` | proved |
| Axiom 6 is not provable in $\mathfrak{B}$ (not in the paper) | `not_B_dne` | proved |
| $A \to (\overline{A} \to B)$ is not provable in $\mathfrak{B}$ (not in the paper) | `not_B_efq` | proved |
| Ch. V: quantifier axioms (63) and formulas (59)–(62) | — | open |

How the formal statements match the paper:

- **Substitution.** Kolmogorov has a rule for substituting formulas for letters. The Lean
  axioms are schemes (one axiom for every choice of $A, B, C$), which has the same effect.
- **Hypotheses.** The paper states the main theorem for mathematics built on axioms
  $\mathfrak{U}_1, \ldots, \mathfrak{U}_k$, and shows that its translations follow from the
  translated axioms $\mathfrak{U}^*$. In Lean these axioms are the hypothesis set $\Gamma$, and the
  conclusion uses the translated set $\Gamma^*$. With $\Gamma$ empty this is the pure logic.
- **The translation.** `kol` follows (48)–(49): a variable $p$ becomes $\neg\neg p$,
  $A \to B$ becomes $\neg\neg(A^* \to B^*)$, and $\overline{A}$ becomes
  $\neg\neg\neg A^*$, as in Kolmogorov's own list (54).
- **The proofs.** Kolmogorov proves his formulas by long chains of substitutions and modus
  ponens (§ 8 of ch. II, ch. III). The Lean proofs first establish the deduction theorem
  (`deduction`) from axioms 1–4 and then argue in natural-deduction style. Only the statements,
  not the individual steps, follow the paper. For the translated axioms (54) the paper proves the
  formulas (55) in $\mathfrak{H}$, justified for judgements of type $A^{\cdot}$; the Lean proof
  derives them directly in $\mathfrak{B}$.
- **The independence results** use a two-valued model in which every negation counts as true.
  Axioms 1–5 hold there, while double negation and $A \to (\overline{A} \to B)$ fail. The paper
  only says that the second "may be provable from other axioms" (ch. II § 4); the model shows
  that it is not provable from axioms 1–5.

## Remarks on the original

Read from the Math-Net.Ru scan. Kept as printed in any translation; listed here, not corrected.

- **p. 653, line after (6).** The restated formula (6) has a stray "$C$" before a brace.
- **p. 654, (18).** The reference on the right is printed as (16); the formula used is (17).
- **p. 657, ch. III § 4.** The inference scheme is printed as
  $\mathfrak{S} \to \mathfrak{T},\ \mathfrak{T} \mid \mathfrak{T}$, for
  $\mathfrak{S},\ \mathfrak{S} \to \mathfrak{T} \mid \mathfrak{T}$.
- **pp. 663, 665, 666.** Contraposition $(A \to B) \to (\overline{B} \to \overline{A})$ is cited as
  (11); it is formula (10).
- **pp. 663, 665.** Quantifier axioms I and II are cited the wrong way round in two places
  (p. 663 "Ax. I" for axiom II; p. 665 "Ax. II" for axiom I, twice).
- **p. 666, (90).** The number is not underlined, though (90) depends on double negation through
  (88) and (89).

## Legacy

The double-negation translation is a basic tool of proof theory. It shows that classical logic
is consistent if intuitionistic (or minimal) logic is, and it underlies Gödel's and Gentzen's
proofs that classical arithmetic is consistent relative to intuitionistic arithmetic. In
computer science it reappears as the continuation-passing-style translation of programs. The
system $\mathfrak{B}$ is the first published axiomatization of minimal logic, eleven years
before Johansson named it (1937).

## To check

- The page range of van Heijenoort's English translation in *From Frege to Gödel* (1967): pp.
  416–437 as cited in secondary literature; the book itself was not checked. Whether the range
  includes the editor's introduction was not checked either.
- The citation (volume 32, issue 4, pp. 646–667, received 30 September 1925, Zbl 51.0048.01) was
  checked against Math-Net.Ru (`sm7425`) and the scan. The date "30–IX–25. Moscow" is printed at
  the end of the article.
- The historical remarks in "Background" and "Legacy" (Gödel 1933, Gentzen, Johansson 1937) are
  standard but were not checked against sources for this entry.
