<!-- AI-drafted translation from the French; equation and footnote numbers follow the original. -->

*Translated from the French original in* Comptes rendus hebdomadaires des séances de l'Académie
des sciences *152 (1911), 244–246, read from the page images of the scan of issue no. 5 (séance du
30 janvier 1911) on the [Internet Archive](https://archive.org/details/comptes-rendus-hebdomadaires-academie-des-sciences_1911-01-30_152_5)
(pages 12–14 of the PDF). Draft translation by Claude (AI), not yet checked by a second reader. Apparent misprints are kept
as printed and flagged in [square-bracketed translator's notes].*

**MATHEMATICAL ANALYSIS. — *On sequences of measurable functions.***
**Note by M. D.-Th. Egoroff.**

Let $f_1(x), f_2(x), \ldots, f_n(x), \ldots$ be a sequence of measurable functions which we shall
suppose convergent, tending to a limit function $f(x)$ at all points $x$ of an interval AB,
except perhaps the points of a set of measure zero. It is well known (¹) that this sequence is at
the same time *convergent in measure*, that is, denoting by $m(n, \varepsilon)$ the measure of the
set of points for which $|f(x) - f_n(x)|$ is greater than a given positive number $\varepsilon$
(as small as one wishes), we have

$$\lim_{n=\infty} m(n, \varepsilon) = 0. \tag{1}$$

M. Lebesgue (²) states an analogous proposition concerning the measure $\mu(n, \varepsilon)$ of the
set $E_n$ of points for which at least one of the differences $f(x) - f_m(x)$, from $m = n$ on, is
greater than (or equal to) $\varepsilon$ in absolute value. This proposition is a simple
consequence of the preceding one, applied to a sequence of functions
$\overline{R}_1(x), \overline{R}_2(x), \ldots, \overline{R}_n(x), \ldots$, the idea of which I
borrow from a memoir of M. Weyl (³), and which are defined by the condition that for each value
of $x$, $\overline{R}_n(x)$ (⁴) is equal to the least upper bound [*limite supérieure*, i.e. the supremum, not the $\limsup$] (⁵) of the sequence of positive
numbers

$$|f(x) - f_n(x)|,\quad |f(x) - f_{n+1}(x)|,\quad \ldots,\quad |f(x) - f_{n+p}(x)|,\quad \ldots. \tag{2}$$

For all points of the interval AB we evidently have

$$\overline{R}_1(x) \geqq \overline{R}_2(x) \geqq \ldots \geqq \overline{R}_n(x) \geqq \overline{R}_{n+1}(x) \geqq \ldots, \tag{3}$$

$$|f(x) - f_m(x)| \leqq \overline{R}_n(x) \quad \text{for} \quad m = n, n+1, \ldots. \tag{4}$$

At all points of convergence of the sequence $f_1, f_2, \ldots, f_n, \ldots$ the sequence
$\overline{R}_1, \overline{R}_2, \ldots, \overline{R}_n, \ldots$ is also convergent, and at these
points we have $\lim_{n=\infty} \overline{R}_n(x) = 0$.

The set $E_n$ of points in question is evidently the set of points for which

$$\overline{R}_n(x) = |\overline{R}_n(x) - 0| \geqq \varepsilon,$$

and consequently the measure $\mu(n, \varepsilon)$ of this set tends to zero as $n$ increases
indefinitely.

Now let $\varepsilon_1, \varepsilon_2, \varepsilon_3, \ldots, \varepsilon_n, \ldots$ be a
decreasing sequence of positive numbers such that $\lim_{n=\infty} \varepsilon_n = 0$; on the
other hand let

$$\eta_1 + \eta_2 + \eta_3 + \ldots + \eta_n + \ldots \tag{5}$$

be a convergent series of positive terms. Consider the sets $E_n^{(i)}$ of points for which
$\overline{R}_n(x) \geqq \varepsilon_i$. Since the measure $\mu(n, \varepsilon_i)$ of this set
tends to zero as $n$ increases indefinitely, one can choose, for each $\varepsilon_i$, a value
$n_i$ such that $\mu(n_i, \varepsilon_i) \leqq \eta_i$. Consider the sequence of sets
$E_{n_1}^{(1)}, E_{n_2}^{(2)}, \ldots, E_{n_i}^{(i)}, \ldots$ and the sum set
$\overline{E}_i$ of the sets $E_{n_i}^{(i)}, E_{n_{i+1}}^{(i+1)}, \ldots$ of this sequence from a
certain value $i$ of the index on. The measure of $\overline{E}_i$ is at most equal to the sum of
the measures

$$\mu(n_i, \varepsilon_i) + \mu(n_{i+1}, \varepsilon_{i+1}) + \ldots,$$

and consequently is less than the remainder $\eta_{i+1} + \eta_{i+2} + \ldots$ of the series (5).
[Translator's note: as printed. The bound $\mu(n_j, \varepsilon_j) \leqq \eta_j$ gives
$\eta_i + \eta_{i+1} + \ldots$; this does not affect the argument.] By taking $i$ sufficiently
large we have a set $\overline{E}_i$ of measure $\eta$ as small as one wishes. At all points of
the interval AB not belonging to $\overline{E}_i$ the sequence $f_1, f_2, \ldots, f_n, \ldots$ is
uniformly convergent. Indeed, at these points we have

$$\overline{R}_{r_i}(x) < \varepsilon_i, \qquad \overline{R}_{r_{i+1}}(x) < \varepsilon_{i+1}, \qquad \ldots,$$

[Translator's note: the subscripts are printed $r_i$, $r_{i+1}$; they should read $n_i$,
$n_{i+1}$.] and consequently

$$|f_m - f| < \varepsilon_{i+p} \quad \text{for} \quad m \geqq n_{i+p}.$$

By taking $p$ large enough one can make all the differences $f - f_m$ from $m = n_{i+p}$ on less
in absolute value than any number $\varepsilon$ one wishes, since the sequence
$\varepsilon_1, \varepsilon_2, \varepsilon_3, \ldots$ converges to zero.

We have therefore proved the following theorem:

THEOREM. — *If one has a sequence of measurable functions convergent at all points of an interval
AB except, perhaps, the points of a set of measure zero, one can always remove from the interval
AB a set of measure $\eta$ as small as one wishes and such that on the complementary set [of
measure $= m(\mathrm{AB}) - \eta$] the sequence is uniformly convergent.*

One may say that every sequence convergent in an interval is *in general* uniformly convergent
(*wesentlich gleichmässig*, following M. Weyl) in the interval.

One sees without difficulty that this theorem admits a great number of applications.

---

(¹) BOREL, *Leçons sur les fonctions de variables réelles*, p. 37. — RIESZ, *Sur les suites de
fonctions mesurables* (*Comptes rendus*, t. 148, p. 1303).

(²) *Leçons sur les séries trigonométriques*, p. 10.

(³) *Mathematische Annalen*, t. LXVII, p. 225.

(⁴) $R_n(x)$ is evidently measurable. [Translator's note: printed without the bar.]

(⁵) At a point of convergence, $\overline{R}_n(x)$ is evidently equal to one of the terms of the
sequence (2).
