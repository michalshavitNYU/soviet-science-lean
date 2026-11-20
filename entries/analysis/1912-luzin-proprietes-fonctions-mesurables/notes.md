## Background

In 1911 Egorov showed that a sequence of measurable functions that converges almost everywhere on
an interval converges uniformly on a closed set whose complement has measure as small as one
likes. Luzin, then a young Moscow mathematician, used this in his Russian memoir *On a
fundamental theorem of the integral calculus* (Matematicheskii Sbornik 28, 1911) to prove what is
now called **Luzin's theorem**: a measurable function is "almost continuous". This note in the
*Comptes Rendus* summarizes the memoir for a French audience. It was prompted by a note of Borel
from February 1912.

## What the note says

Luzin calls the following the **C-property** of a function $f$ on $0 \le x \le 1$: for every
$\varepsilon > 0$ there is a perfect, nowhere dense set $P$ such that

1. $f$ is continuous on $P$, relative to $P$ (only points of $P$ are compared), and
2. the measure of $P$ is greater than $1 - \varepsilon$.

The note then goes in four steps.

- **Baire class 1.** A function of Baire class 1 is a pointwise limit of polynomials. Egorov's
  theorem makes the convergence uniform on a large perfect set, so the limit is continuous there:
  functions of class 1 have the C-property.
- **Limits.** If every $f_n$ has the C-property and $f_n \to f$ almost everywhere, then $f$ has
  it. Take Egorov's set $P_0$ with measure $> 1 - \varepsilon/4$ and sets $P_n$ for the $f_n$
  with measure $> 1 - \varepsilon/2^{n+2}$. On the intersection $E$ every $f_n$ is continuous and
  the convergence is uniform, so $f$ is continuous on $E$, and $E$ has measure
  $> 1 - \varepsilon/2$. A perfect, nowhere dense subset of $E$ of measure $> 1 - \varepsilon$
  finishes the proof. So all functions of Baire's classification have the C-property.
- **General theorem.** Every measurable function has the C-property, and every function with
  the C-property is measurable. The note states this without proof.
- **Consequences.** Every measurable function is, outside a null set, the sum of an absolutely
  convergent series of polynomials (a measure-theoretic version of Weierstrass's approximation
  theorem). Then two theorems from the memoir: (I) no continuous function has derivative
  $+\infty$ or $-\infty$ on a set of positive measure; (II) every measurable function that is
  finite almost everywhere is almost everywhere the derivative of a continuous function.

"Ensemble non dense", in the language of Baire and Borel, means *nowhere dense*; it is
translated that way.

## What the Lean file proves

| Note | Lean | Status |
|---|---|---|
| the C-property, property (C) | `CProperty` | definition |
| general theorem: measurable ⇒ C-property | `cProperty_of_aemeasurable` | proved |
| converse: C-property ⇒ measurable | `aemeasurable_of_cProperty` | proved |
| measurable ⇔ C-property | `aemeasurable_iff_cProperty` | proved |
| a.e. limit of functions with the C-property has it | `cProperty_of_tendsto` | proved |
| modern form: $f = g$ off a set of measure $< \varepsilon$, $g$ continuous on $\mathbb R$ | `exists_continuous_eq_off` | proved |
| a series of polynomials converging absolutely to $f$ a.e. | `exists_polynomial_series` | proved |
| Theorem I (no infinite derivative on a set of positive measure) | — | open |
| Theorem II (every a.e. finite measurable function is an a.e. derivative) | — | open |

How the formal statements match the note:

- The interval is $[0, 1]$ and "measure" is Lebesgue measure. A function on the interval is a
  function $f : \mathbb R \to \mathbb R$; its values outside $[0, 1]$ never matter.
- "Measurable" means Lebesgue measurable on $[0, 1]$. In Lean this is
  `AEMeasurable f (volume.restrict (Icc 0 1))`: $f$ agrees almost everywhere on $[0, 1]$ with a
  Borel function, which for real-valued functions is the same thing.
- "Perfect" is Mathlib's `Perfect` (closed, with no isolated points); "nowhere dense" is
  `IsNowhereDense`; "continuous on $P$ relative to $P$" is `ContinuousOn f P`; and
  "the measure of $P$ exceeds $1 - \varepsilon$" is `ENNReal.ofReal (1 - ε) < volume P`.
- The note's functions are real-valued. Infinite values first appear in Theorem II, which is not
  formalized.
- "Converges absolutely to $f(x)$" is formalized as: $\sum_n |p_n(x)| < \infty$ and
  $\sum_n p_n(x) = f(x)$. The Lean series starts at $n = 0$ instead of $n = 1$.
- `exists_continuous_eq_off` is not in the note; it is the form of Luzin's theorem found in most
  textbooks, and it follows from the note's form by Tietze's extension theorem.

## Idea of the proofs

Mathlib does not contain Luzin's theorem, so the proofs are written in the Lean file. They do
not follow Luzin's route through Egorov's theorem and Baire classes. They use a short argument
based on the regularity of Lebesgue measure.

1. *A closed set where $f$ is continuous.* First let $f$ be a Borel function. Fix a countable
   family of open intervals $U$ generating the topology of $\mathbb R$ (for example, intervals
   with rational endpoints). For each $U$, choose a closed set inside $f^{-1}(U)$ and a closed
   set inside its complement, both missing only a small part of $[0, 1]$; the errors are chosen
   to add up to less than $\varepsilon$. Let $K$ be the set of points that lie in one of the two
   closed sets for every $U$. Then $K$ is closed, and on $K$ the set $f^{-1}(U)$ is the
   complement of a closed set, hence relatively open. So $f$ is continuous on $K$. If $f$ is only
   Lebesgue measurable, it agrees with a Borel function outside a null set; cover that set by an
   open set of small measure and remove it from $K$.
2. *Nowhere dense.* Remove from $K$ a small open ball around every rational number, with radii
   chosen so that the balls have total length less than $\varepsilon$. What is left contains no
   rational, so it contains no interval.
3. *Perfect.* By the Cantor–Bendixson theorem, a closed subset of $\mathbb R$ is a perfect set
   plus a countable set. A countable set has measure zero, so the perfect part has the same
   measure.
4. *Converse.* Take $P_n$ for $\varepsilon = 1/(n+1)$. The function $f$ is measurable on each
   $P_n$, being continuous there, and the union of the $P_n$ fills $[0, 1]$ up to a null set.
5. *Polynomial series.* For each $n$ take a continuous $g_n$ equal to $f$ outside a set of
   measure $< 2^{-n}$, then a polynomial $q_n$ within $2^{-n}$ of $g_n$ on $[0, 1]$
   (Weierstrass). By the Borel–Cantelli lemma almost every $x$ lies in only finitely many of the
   exceptional sets, so $|q_n(x) - f(x)| < 2^{-n}$ for all large $n$. The series with terms
   $p_0 = q_0$ and $p_n = q_n - q_{n-1}$ has partial sums $q_n$ and terms bounded by
   $3 \cdot 2^{-n}$ for large $n$, so it converges absolutely to $f(x)$.

## History

Luzin's theorem made the phrase "a measurable function is nearly continuous" precise; it is the
second of Littlewood's "three principles" of real analysis.

## To check

- The citation (vol. 154, pp. 1688–1690, session of 17 June 1912, presented by Émile Picard,
  author printed as "N. Lusin") was read from the scan on the Internet Archive. The Gallica scan
  was not reached (the site refused automated access), so its link is not given; it would be good
  to add it.
- The citation of the Russian memoir (Matematicheskii Sbornik 28:2, 1911) is taken from the note
  itself; its page numbers were not checked.
- Earlier versions of the theorem are often credited to Lebesgue (1903) and Vitali (1905). This
  was not checked against the sources.
- Whether a published English translation of this note exists. None was found.
- The exponent in $\operatorname{Mes} P_n > 1 - \varepsilon/2^{n+2}$ is faint in the scan; the
  reading $n + 2$ is the one consistent with the sum that follows it.
