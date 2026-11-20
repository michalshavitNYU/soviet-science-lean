<!-- AI-drafted translation from the Russian; equation numbers follow the original. -->

*Translated from the Russian original as scanned on [Math-Net.Ru](https://www.mathnet.ru/rus/im3359), read page by page; every formula was read from the scan. Draft translation by Claude (AI), not yet checked by a second reader. Apparent misprints are kept as printed and flagged in [square-bracketed translator's notes].*

**A. N. Kolmogorov**

**ON THE STATISTICAL THEORY OF THE CRYSTALLIZATION OF METALS**

(*Presented by Academician S. N. Bernstein*)

*Under certain schematic but nevertheless fairly general assumptions, a rigorous solution is
given of the problem of the rate at which the process of crystallization proceeds.*

For metallurgy it is of essential importance to study the process of crystal growth when the
centres of crystallization form *at random*. A known difficulty here is to account for the
*collisions* of the grains of crystalline substance that arise around the individual centres of
crystallization. These collisions destroy the regular shape of the grains, stopping their growth
in some directions. The works published so far by F. Göler and G. Sachs (¹), G. Tammann (²),
B. V. Stark, I. L. Mirkin and A. N. Romanovsky (³) and others give only crude approximate formulas
for the growth of the crystalline mass. In the present note I give, under certain fairly broad
assumptions, an *exact* formula for the probability $p(t)$ that a point $P$, chosen at random
in a volume filled with substance subject to crystallization, falls within the time interval
of crystallization inside the already crystallized mass. With quite sufficient approximation one
may take the fraction of the substance crystallized during the time interval $t$ to be equal to
$p(t)$ as well. In conclusion I determine the number of centres of crystallization that form
during the whole process of crystallization.

I take this opportunity to express my gratitude to I. L. Mirkin, who interested me in the
problem solved here and kindly provided all the necessary material.

## § 1. Mathematical statement of the problem

A volume $V$ is given. At the beginning ($t = 0$) it is entirely occupied by the "mother phase".
After a time interval $t$, a certain part $V_1(t)$ of the volume $V$ is occupied by crystallized
substance. The volume $V_1(t)$ grows with time $t$ in the following way:

1. New centres of crystallization arise in the free part $V - V_1$ of the volume $V$. For any
volume $V' < V - V_1$, the probability that *one* centre of crystallization forms in this volume
during the time interval between $t$ and $t + \Delta t$ equals
$$\alpha(t)\, V' \Delta t + o(\Delta t),$$
and the probability of *more than one* centre equals $o(\Delta t)$, where $o(\Delta t)$ denotes a
quantity infinitely small compared with $\Delta t$. These probabilities do not depend on the
distribution of the centres of crystallization formed before the moment $t$, provided only that
this distribution guarantees (see below) that the volume $V'$ is free of crystalline mass at the
moment $t$.

2. Around the newly formed centres of crystallization, and around the whole crystallized mass,
this mass grows with linear speed
$$c(t, n) = k(t) \cdot c(n),$$
depending on the time $t$ and the direction $n$. We assume that the ends of the vectors of
length $c(n)$, laid off from the origin in the direction $n$, form a convex surface.

Under the conditions stated, an essential restriction is that the linear growth speed
$c(t, n)$, although it may depend on the direction $n$, must depend on it in one and the same
way at all points. In other words, the formulas derived below are valid either under the
simplifying assumption of uniform growth in all directions, or for crystals of arbitrary shape
that are identically oriented in space.

## § 2. Determination of the probability $p(t)$

Introduce the quantity $c$ defined by
$$c^3 = \frac{1}{4\pi} \int_S c^3(n)\, d\sigma,$$
where the integration is over the surface of the unit sphere $S$ centred at the origin.
Evidently the volume of a crystal growing freely around a centre formed at the moment $t_0$
reaches, by the moment $t > t_0$, the value
$$\frac{4\pi}{3}\, c^3 \Big( \int_{t_0}^{t} k(\tau)\, d\tau \Big)^3 .$$

Now consider an arbitrary point $P$ of the volume $V$ lying at a distance greater than
$$\max c(n) \int_0^t k(\tau)\, d\tau$$
from the boundary of the volume $V$.

For the point $P$ to lie inside the crystallized mass by the moment $t$ it is necessary and
sufficient that at some moment $t' < t$, at some point $P'$ lying at a distance from $P$ less
than
$$c(\bar n) \int_{t'}^{t} k(\tau)\, d\tau,$$
where $\bar n$ denotes the direction of $\overline{P'P}$, a centre of crystallization has formed.
For fixed $t'$ the volume $V'(t')$ occupied by the points $P'$ satisfying these conditions equals
$$V'(t') = \frac{4\pi}{3}\, c^3 \Big( \int_{t'}^{t} k(\tau)\, d\tau \Big)^3 .$$

The probability that during the time interval $\Delta t'$ a centre of crystallization forms in the
volume $V'(t')$ equals
$$\alpha(t')\, V'(t')\, \Delta t' + o(\Delta t'),$$
and the probability that this does *not* happen equals
$$1 - \alpha(t')\, V'(t')\, \Delta t' + o(\Delta t').$$
Therefore the probability that the point $P$ is *not* included in the crystallized mass by the
moment $t$ equals
$$q(t) = \prod_{i=1}^{s} \big\{ 1 - \alpha(t_i)\, V'(t_i)\, \Delta t' \big\} + o(1), \tag{1}$$
where $t = s\,\Delta t'$, $t_i = i\,\Delta t'$, and $o(1)$ is infinitely small for infinitely
small $\Delta t'$.

Taking logarithms in (1), we obtain:
$$\log q(t) = \sum_{i=1}^{s} \alpha(t_i)\, V'(t_i)\, \Delta t' + o(1)
= -\int_0^t \alpha(t')\, V'(t')\, dt' =
= -\frac{4\pi}{3}\, c^3 \int_0^t \alpha(t') \Big( \int_{t'}^{t} k(\tau)\, d\tau \Big)^3 dt'. \tag{2}$$
[Translator's note: as printed, the sum carries no minus sign; it should read
$-\sum_{i=1}^{s} \dots$, consistent with the following integrals.]

For the required probability
$$p(t) = 1 - q(t)$$
that the point $P$ is included in the crystallized mass we finally obtain
$$p(t) = 1 - e^{-\frac{4\pi}{3} c^3 \Omega}, \tag{3}$$
where
$$\Omega = \int_0^t \alpha(t') \Big( \int_{t'}^{t} k(\tau)\, d\tau \Big)^3 dt'. \tag{4}$$

## § 3. Conclusions

For a volume $V$ sufficiently large compared with the sizes of individual grains one may put
$V_1(t) = V p(t)$, or by (3)
$$V_1(t) = V \Big( 1 - e^{-\frac{4\pi}{3} c^3 \Omega} \Big), \tag{5}$$
where $\Omega$ is determined by formula (4). Formula (5) for the volume $V_1(t)$ of the mass
crystallized during the time $t$ solves the first of the problems posed in the introduction.
If $\alpha(t)$ and $c(t, n)$ do not depend on time, we may put
$$\alpha(t) = \alpha, \qquad k(t) = 1.$$
In this case
$$\Omega = \frac{\alpha t^4}{4} \tag{4a}$$
and formula (5) gives
$$V_1(t) = V \Big( 1 - e^{-\frac{\pi}{3} c^3 \alpha t^4} \Big). \tag{5a}$$
For the number $N(t)$ of centres of crystallization formed during the time $t$ the following
formula holds for a sufficiently large volume $V$:
$$N(t) = V \int_0^t \alpha(\tau)\, q(\tau)\, d\tau. \tag{6}$$
For constant $\alpha(t) = \alpha$ and $k = 1$ we obtain from (6)
$$N(t) = V \alpha \int_0^t e^{-\frac{\pi}{3} c^3 \alpha \tau^4}\, d\tau,$$
or
$$N(t) = V \sqrt[4]{\frac{3\alpha^3}{\pi c^3}} \int_0^x e^{-\xi^4}\, d\xi, \tag{6a}$$
where
$$x = \sqrt[4]{\frac{\pi c^3 \alpha}{3}}\; t .$$
For $t = +\infty$ formulas (6) and (6a) give the total number of centres of crystallization
arising during the whole process. In particular, for constant $\alpha(t) = \alpha$ and $k = 1$ we
obtain:
$$N(+\infty) = V \sqrt[4]{\frac{3\alpha^3}{\pi c^3}} \int_0^\infty e^{-\xi^4}\, d\xi
\sim 0.9\, V \Big( \frac{\alpha}{c} \Big)^{\frac{4}{3}}. \tag{7a}$$
[Translator's note: the exponent is printed as $\frac43$; the preceding exact expression gives
$(\alpha/c)^{3/4}$. Also $(3/\pi)^{1/4}\int_0^\infty e^{-\xi^4}d\xi = (3/\pi)^{1/4}\,\Gamma(5/4)
\approx 0.89$.]

We note also the special case in which all centres of crystallization form at the very
beginning, on average $\beta$ per unit volume. The corresponding formulas are obtained from the
general ones by a passage to the limit. Instead of (4) we obtain
$$\Omega = \beta \Big( \int_0^t k(\tau)\, d\tau \Big)^3, \tag{4b}$$
formula (5) is preserved, and formula (6) is replaced, for any $t > 0$, by the trivial equality
$N = V\beta$. If moreover we assume $k = 1$ (i.e. $c(t, n)$ independent of $t$), we obtain
$$\Omega = \beta t^3, \tag{4c}$$
$$V_1(t) = V \Big( 1 - e^{-\frac{4\pi}{3} c^3 \beta t^3} \Big). \tag{5c}$$

*Mathematical Institute, Moscow State University.* Received 20.IV.1937.

### Literature

1. Göler F. und Sachs G., Zeitschr. f. Physik, **77**, 281, 1932.
2. Tammann G., Zeitschr. anorg. Chemie, **214**, 407, 1933.
3. Stark B. V., Mirkin I. L., Romanovsky A. N., Metallovedenie i termicheskaya obrabotka
   [Metallography and heat treatment], *Trudy Moskovskogo instituta stali* [Transactions of the
   Moscow Institute of Steel], **7**, 5–38, 1935.

---

**A. Kolmogoroff. Zur Statistik der Kristallisationsvorgänge in Metallen.**
*Summary* (translated from the German).

The author gives a rigorous solution of the following schematized problem: in unbounded space,
centres of crystallization arise at random, in such a way that in every volume $V$ which at time
$t$ remains free of the crystallized mass a new centre arises during the time interval
$(t, t + dt)$ with probability $\alpha V dt$. The crystallized mass grows continuously in all
directions with speed $c$. Sought is the probability that an arbitrarily chosen point $P$ of
space is included in the crystallized mass at time $t$ (the process begins at $t = 0$). The
solution is given by the formula
$$p(t) = 1 - e^{-\frac{\pi}{3} c^3 \alpha t^4}.$$
The problem can also be solved for variable $\alpha$ and $c$.
