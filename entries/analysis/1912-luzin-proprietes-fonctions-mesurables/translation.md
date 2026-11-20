<!-- AI-drafted translation from the French; layout and the label (C) follow the original. -->

*Translated from the French original in Comptes Rendus de l'Académie des Sciences 154 (1912), pp. 1688–1690, as scanned on the [Internet Archive](https://archive.org/details/comptes-rendus-hebdomadaires-academie-des-sciences_1912-06-17_154_25) (issue of 17 June 1912, PDF pages 28–30), read page by page; every formula was read from the scan. Draft translation by Claude (AI), not yet checked by a second reader. Translator's remarks are in [square brackets].*

**MATHEMATICAL ANALYSIS. — *On the properties of measurable functions.***
Note by M. N. **Lusin**, presented by M. Émile Picard.

Reading the interesting Note of M. Borel (*Comptes rendus*, 12 February 1912) gave me the idea
of summarizing here the results on measurable functions that I have already published in Russian
in the *Recueil de la Société mathématique de Moscou* (vol. XXVIII, 2, 1911), in the memoir
entitled *On a fundamental theorem of the integral calculus*.

Let $f_1(x), f_2(x), \dots, f_n(x), \dots$ be a sequence of measurable functions which we assume
to be convergent and to tend to a limit function $f(x)$ for all points $x$ of the interval
$0 \le x \le 1$, except perhaps the points of a set of measure zero. By an important theorem of
M. Egoroff (*Comptes rendus*, 30 January 1911), there exists a perfect and nowhere dense
[*non dense*] set $P$ with the following properties:

1° The sequence $f_1, f_2, \dots, f_n, \dots$ converges *uniformly* to $f(x)$ on this set $P$.

2° The measure of $P$ is greater than $1 - \varepsilon$ ($\varepsilon > 0$ being as small as one
wishes).

Supposing that $f_n(x)$ is a polynomial ($n = 1, 2, 3, \dots$), we obtain the following result:
if $f(x)$ is a function defined in the interval $0 \le x \le 1$ of class 1 (in the sense of
M. Baire),

> *there exists in this interval a perfect and nowhere dense set $P$ with the properties:*
>
> *1° The function $f(x)$ is continuous on $P$ (relative to $P$);*
>
> *2° The measure of $P$ is greater than $1 - \varepsilon$, $\varepsilon > 0$ as small as one
> wishes.* $\qquad$ (C)

Let us denote this property of the function $f(x)$ by "C-property". We shall have the theorem:

*If every function of the sequence $f_1, f_2, \dots, f_n, \dots$ possesses the "C-property", the
limit function $f(x)$ also possesses the "C-property".*

Indeed, let us take, by the theorem of M. Egoroff, a perfect and nowhere dense set $P_0$ on which
the sequence converges uniformly and $\operatorname{Mes} P_0 > 1 - \frac{\varepsilon}{2^2}$,
$\varepsilon > 0$ as small as one wishes. Let us consider further, by virtue of the
"C-property", a perfect and nowhere dense set $P_n$ ($n = 1, 2, 3, \dots$) on which $f_n(x)$ is
continuous (relatively) and $\operatorname{Mes} P_n > 1 - \frac{\varepsilon}{2^{n+2}}$.
[The exponent $n+2$ is faint in the scan; it is the reading consistent with the sum that follows.]
All the points common to all the sets $P_0, P_1, P_2, \dots$ evidently form a measurable set $E$,
and
$$\operatorname{Mes} E > 1 - \left(\frac{\varepsilon}{2^2} + \frac{\varepsilon}{2^3} + \dots\right)
= 1 - \frac{\varepsilon}{2}.$$
Consequently the set $E$ contains a perfect and nowhere dense set $P$ such that
$\operatorname{Mes} P > 1 - \varepsilon$. One sees that this set $P$ satisfies the "C-property".
(Q. E. D.)

It follows that the "C-property" belongs not only to the functions of class 1 but to all the
functions of M. Baire's classification. But one can see, moreover, that every measurable function
possesses this "C-property" and, conversely, that every function $f(x)$ possessing the
"C-property" is a measurable function.

We thus find this general theorem:

*If $f(x)$ is a measurable function defined in the interval $0 \le x \le 1$, there exists in this
interval a perfect and nowhere dense set $P$ enjoying the properties:*

*1° The function $f(x)$ is continuous on $P$ (relative to $P$);*

*2° The measure of $P$ is greater than $1 - \varepsilon$, $\varepsilon > 0$ as small as one
wishes.*

As a consequence we obtain:

*If $f(x)$ is a measurable function defined in the interval $0 \le x \le 1$, there exists a
series of polynomials $\sum_{n=1} p_n(x)$ converging absolutely to the function $f(x)$ for all
points of the interval $0 \le x \le 1$, except perhaps the points of a set of measure zero.*

[The summation sign carries only the lower limit $n = 1$ in the original.]

One sees that this result is the generalization of the celebrated theorem of Weierstrass–Picard
on the representation of continuous functions.

These results have allowed me to prove the two following theorems:

I. *There exists no continuous function $F(x)$ having $\frac{dF}{dx} = +\infty$ or
$\frac{dF}{dx} = -\infty$ on a set of points of* non-zero *measure.*

II. General theorem. — *If $f(x)$ is a measurable function defined in the interval
$0 \le x \le 1$ and finite everywhere except perhaps at the points of a set of measure zero,
there exists a function $F(x)$ continuous in the whole interval $0 \le x \le 1$ such that it has
$f(x)$ as its ordinary derivative at all points, except perhaps at the points of a set of measure
zero.*

One can thus say that the problem of finding primitive functions is solved when sets of measure
zero are neglected.
