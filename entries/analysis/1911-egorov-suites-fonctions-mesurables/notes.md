## Background

Dmitri Fyodorovich Egorov (1869–1931) led the Moscow school of real-function theory; Luzin was
his student. This note, presented to the Paris Academy on 30 January 1911 and signed with the
French spelling "D.-Th. Egoroff", contains the theorem now named after him. Carlo Severini had
published an equivalent result in Italian in 1910, and the theorem is sometimes called the
Severini–Egorov theorem.

## What the note does

Let $f_1, f_2, \ldots$ be measurable functions on an interval AB that converge to $f$ outside a
set of measure zero.

1. It recalls that the sequence converges in measure: the measure $m(n, \varepsilon)$ of the set
   where $|f - f_n| > \varepsilon$ tends to $0$ (Eq. (1), credited to Borel and F. Riesz).
2. It recalls a proposition of Lebesgue: the measure $\mu(n, \varepsilon)$ of the set $E_n$ where
   $|f - f_m| \ge \varepsilon$ for *some* $m \ge n$ also tends to $0$. To derive it from (1),
   Egorov borrows from Weyl the functions
   $$\overline{R}_n(x) = \sup_{m \ge n} |f(x) - f_m(x)|,$$
   which decrease in $n$ (Eq. (3)), dominate every later difference (Eq. (4)), and tend to $0$ at
   every point of convergence. Then $E_n$ is the set where $\overline{R}_n \ge \varepsilon$, and
   (1) applied to the sequence $\overline{R}_n$ gives Lebesgue's proposition.
3. The main step. Fix $\varepsilon_i \downarrow 0$ and a convergent series $\sum \eta_i$ of
   positive terms. For each $i$ pick $n_i$ with $\mu(n_i, \varepsilon_i) \le \eta_i$. The union
   $\overline{E}_i$ of the sets $\{\overline{R}_{n_j} \ge \varepsilon_j\}$ for $j \ge i$ has
   measure at most the tail $\sum_{j \ge i} \eta_j$, which is small for large $i$. Off
   $\overline{E}_i$ we have $|f - f_m| < \varepsilon_j$ for all $m \ge n_j$ and every $j \ge i$,
   which is uniform convergence.
4. The theorem: one can remove from AB a set of measure $\eta$, as small as one wishes, so that
   the sequence converges uniformly on the rest. Egorov adds that, in Weyl's phrase, every
   convergent sequence is "essentially uniformly" (*wesentlich gleichmässig*) convergent.

## What the Lean file proves

| Paper | Lean | Status |
|---|---|---|
| Théorème: uniform convergence off a set of measure $\le \eta$; the rest has measure $\ge m(AB) - \eta$ | `egorov` | proved |
| (1): $m(n, \varepsilon) \to 0$ | `measure_gt_tendsto_zero` | proved |
| Lebesgue's proposition: $\mu(n, \varepsilon) \to 0$ | `measure_tail_tendsto_zero` | proved |
| (3): $\overline{R}_1 \ge \overline{R}_2 \ge \ldots$ | `Rbar_antitone` | proved |
| (4): $\lvert f - f_m\rvert \le \overline{R}_n$ for $m \ge n$ | `le_Rbar` | proved |
| $\overline{R}_n(x) \to 0$ at points of convergence | `Rbar_tendsto_zero` | proved |
| Footnote (4): $\overline{R}_n$ is measurable | `measurable_Rbar` | proved |

How the formal statements match the paper:

- The interval AB is the closed interval $[a, b]$ and "measure" is Lebesgue measure. The
  sequence is `f n`; the paper's limit $f$ is called `g` in Lean, to keep the letter `f` for the
  sequence.
- "Convergent at all points of AB except perhaps a set of measure zero" is stated literally:
  for almost every $x$, if $x \in [a, b]$ then $f_n(x) \to g(x)$.
- The $f_n$ are assumed Borel measurable. The limit $g$ is **not** assumed measurable in the
  theorem, nor in (1) and Lebesgue's proposition: the proof replaces $g$ by a measurable function
  equal to it off a null set and adds that null set to the removed set. Only
  `measurable_Rbar` assumes $g$ measurable (in the paper this follows because $g$ is an
  almost-everywhere limit of measurable functions and Lebesgue measure is complete).
- The theorem gives a removed set of measure at most $\eta$, which is what "as small as one
  wishes" means, and states the bracket "[of measure $= m(AB) - \eta$]" as an inequality
  $\ge (b - a) - \eta$.
- $\overline{R}_n(x)$ is a supremum in $[0, \infty]$, so it makes sense even where the numbers
  (2) are unbounded.
- The proofs differ from the paper's. The theorem cites Mathlib's
  `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto` (by Kexing Ying), whose proof follows
  Egorov's step 3. Lebesgue's proposition and (1) are then derived *from* the theorem: for large
  $n$ the set $E_n$ lies inside the small removed set. The paper goes the other way.

## Remarks on the text

- **"Limite supérieure"** in 1911 French means the least upper bound (the supremum), not the
  $\limsup$. Footnote (5) and Eqs. (3)–(4) confirm this reading.
- **Footnote (5)** says that at a point of convergence $\overline{R}_n(x)$ equals one of the terms
  of (2). This is true (a sequence of nonnegative numbers tending to $0$ attains its supremum), and
  it is what makes "$E_n$ is the set where $\overline{R}_n \ge \varepsilon$" correct at points of
  convergence. At other points the two sets can differ; they form a null set, so the measures
  agree.

## Errata in the original

- **Footnote (4)** prints $R_n(x)$ without the bar.
- **Tail of the series (5).** The measure of $\overline{E}_i$ is said to be less than
  $\eta_{i+1} + \eta_{i+2} + \ldots$; the bound $\mu(n_j, \varepsilon_j) \le \eta_j$ gives
  $\eta_i + \eta_{i+1} + \ldots$. The argument is unaffected.
- **Subscripts $r_i$.** The display after "at these points we have" prints
  $\overline{R}_{r_i}(x) < \varepsilon_i$, $\overline{R}_{r_{i+1}}(x) < \varepsilon_{i+1}$;
  the subscripts should be $n_i$, $n_{i+1}$.

## To check

- **Gallica.** The scan read for the translation is the Internet Archive copy of issue 5 of
  t. 152. Wikipedia cites the Gallica copy as `https://gallica.bnf.fr/ark:/12148/bpt6k3105c/f244`;
  Gallica refused automated access, so that link (and whether `f244` is printed page 244) was
  not checked.
- **Title.** The note's printed title is *Sur les suites de fonctions mesurables* ("de", not
  "des", as some citations give). Checked on the scan.
- **Citation.** Volume 152, pages 244–246, séance du 30 janvier 1911: checked on the scan.
  The Jahrbuch review number JFM 42.0423.01 is quoted by Wikipedia and was not checked.
- **English translation.** No published English translation was found; this was not searched
  thoroughly.
- **References in the footnotes** (Borel, *Leçons sur les fonctions de variables réelles*, p. 37;
  Riesz, C. R. 148, p. 1303; Lebesgue, *Leçons sur les séries trigonométriques*, p. 10; Weyl,
  Math. Ann. 67, p. 225) are transcribed from the scan but were not looked up.
