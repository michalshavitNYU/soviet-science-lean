## Background

When a metal solidifies, crystals start at random points ("centres of crystallization") and
grow until they run into one another. Engineers in the 1930s (Göler and Sachs, Tammann, and in
Moscow Stark, Mirkin and Romanovsky) had only rough formulas for how fast the solid fraction
grows, because the collisions between growing grains were hard to account for. Kolmogorov,
asked by I. L. Mirkin, gave an exact answer in this five-page note. The same result was found
independently by Johnson and Mehl (1939) and Avrami (1939–41); the theory is now known as
Kolmogorov–Johnson–Mehl–Avrami (KJMA).

## The model

The note has three sections.

**§1, assumptions.** At time $t = 0$ a volume $V$ is entirely liquid. In any part $V'$ of the
volume that is still liquid, a new centre appears between $t$ and $t + \Delta t$ with
probability $\alpha(t) V' \Delta t + o(\Delta t)$, independently of what happened before. Around
every centre the solid grows with linear speed $c(t, n) = k(t)\, c(n)$ in the direction $n$,
and this law is the same at every point (so either growth is isotropic, or all crystals have
the same shape and orientation).

**§2, the key idea.** Instead of tracking colliding grains, fix a point $P$ and ask when it
becomes solid. It is solid at time $t$ exactly when some centre has appeared, at an earlier time
$t'$, close enough to $P$ that a crystal starting there would have reached $P$ by time $t$.
Collisions do not matter for this question: if the region near $P$ had already been swallowed
by another grain, $P$ is solid anyway. For each $t'$ these starting points fill a region of
volume
$$V'(t') = \frac{4\pi}{3} c^3 \Big(\int_{t'}^t k(\tau)\, d\tau\Big)^3,$$
where $c^3$ is the average of $c(n)^3$ over directions. The probability that no centre appears
there in any of the small time steps is a product (Eq. (1)), whose logarithm becomes an integral
(Eq. (2)). The result is
$$p(t) = 1 - e^{-\frac{4\pi}{3} c^3 \Omega}, \qquad
\Omega = \int_0^t \alpha(t') \Big(\int_{t'}^t k(\tau)\, d\tau\Big)^3 dt' . \qquad (3), (4)$$
In modern language: the centres form a Poisson process in space-time, $\frac{4\pi}{3} c^3 \Omega$
is the expected number of centres in the "cone" of space-time points that would already cover
$P$, and $p(t)$ is one minus the probability that this cone is empty.

**§3, consequences.** For a large volume the crystallized volume is $V_1(t) = V p(t)$ (5). With
constant rate and speed ($\alpha(t) = \alpha$, $k = 1$), $\Omega = \alpha t^4/4$ (4a) and
$$V_1(t) = V\big(1 - e^{-\frac{\pi}{3} c^3 \alpha t^4}\big). \qquad (5a)$$
The number of centres is $N(t) = V \int_0^t \alpha(\tau) q(\tau)\, d\tau$ (6), where
$q = 1 - p$; for constant data a change of variables gives (6a), and letting $t \to \infty$
gives the total number of grains (7a). Finally, if all centres appear at $t = 0$ with density
$\beta$, then $\Omega = \beta(\int_0^t k)^3$ (4b), and for $k = 1$, $\Omega = \beta t^3$ (4c) and
$V_1(t) = V(1 - e^{-\frac{4\pi}{3} c^3 \beta t^3})$ (5c).

## What the Lean file proves

| Paper | Lean | Status |
|---|---|---|
| (4a): $\Omega = \alpha t^4/4$ | `Omega_const` | proved |
| $\int_0^t I c_d (v(t-s))^d\, ds = I c_d v^d t^{d+1}/(d+1)$ (the same integral in dimension $d$) | `nucleation_integral_dim` | proved |
| (5a): $p(t) = 1 - e^{-\frac{\pi}{3} c^3 \alpha t^4}$ | `crystallized_const` | proved |
| (4c): $\Omega = \beta t^3$ | `Omega_instant_one` | proved |
| (5c): $p(t) = 1 - e^{-\frac{4\pi}{3} c^3 \beta t^3}$ | `crystallized_instant` | proved |
| $1 - e^{-a t^n}$ is $0$ at $t = 0$ | `fraction_zero` | proved |
| $1 - e^{-a t^n}$ is nondecreasing for $t \ge 0$ ($a \ge 0$) | `fraction_monotoneOn` | proved |
| $1 - e^{-a t^n} \to 1$ as $t \to \infty$ ($a > 0$, $n \ge 1$) | `fraction_tendsto_one` | proved |
| (6) ⇒ (6a): $\int_0^t e^{-\lambda^4\tau^4} d\tau = \lambda^{-1}\int_0^{\lambda t} e^{-\xi^4} d\xi$ | `count_substitution` | proved |
| (7a): $N(t) \to V (3\alpha^3/(\pi c^3))^{1/4}\, \Gamma(5/4)$ | `total_count` | proved |
| Poisson count with mean $r$ is $0$ with probability $e^{-r}$ | `void_prob` | proved |
| (3) in Poisson form: $P$ uncrystallized with probability $e^{-\frac{4\pi}{3}c^3\Omega}$ | `uncrystallized_prob` | proved |
| independent regions: void probabilities multiply | `void_prob_add` | proved |
| (1) ⇒ (2): $\prod_i (1 - \alpha V' \Delta t') \to e^{-\int \alpha V'}$ | — | open |

How the formal statements match the paper:

- $\Omega$ is defined exactly as in (4), with interval integrals; $p(t)$ exactly as in (3).
- The paper derives the Poisson structure from the infinitesimal assumption of §1 through the
  product (1). The Lean file does not formalize that limit. Instead, `uncrystallized_prob`
  assumes what the limit yields: the number of centres in the covering cone is Poisson with
  mean $\frac{4\pi}{3}c^3\Omega$. It then concludes that the probability of "$P$ not yet
  crystallized" is $1 - p(t)$. The Poisson law is Mathlib's `poissonMeasure`; `void_prob_add`
  uses Mathlib's theorem that independent Poisson variables add.
- (7a) is proved in exact form, using Mathlib's evaluation
  $\int_0^\infty e^{-b x^p}dx = b^{-1/p}\,\Gamma(1/p + 1)$, so
  $\int_0^\infty e^{-\xi^4}d\xi = \Gamma(5/4)$. The numerical constant $0.9$ is not formalized.

## Errata in the original

- **Eq. (2).** The sum is printed as $\sum \alpha(t_i) V'(t_i) \Delta t'$ without a minus sign;
  it should be $-\sum$, as the integrals that follow show.
- **Eq. (7a).** The approximate value is printed as $\sim 0.9\, V (\alpha/c)^{4/3}$. The exact
  expression just before it is $V (3/\pi)^{1/4} \Gamma(5/4)\, (\alpha/c)^{3/4}$, so the exponent
  should be $3/4$. The constant $(3/\pi)^{1/4}\Gamma(5/4) \approx 0.89$ agrees with "0.9".

## Legacy

The formula $1 - e^{-k t^n}$ (the "Avrami equation", with $n = 4$ for constant nucleation and
$n = 3$ for nucleation at $t = 0$ in three dimensions) is standard in metallurgy, polymer
science and the theory of phase transitions. The "look at a single point" argument is an early
example of the void probability of a Poisson process.

## To check

- The page range of the English translation in *Selected Works of A. N. Kolmogorov*, Vol. II
  (Kluwer, 1992), and its number in that volume. A contents listing found online gives the
  title "On the statistical theory of metal crystallization"; the pages were not verified.
- The citation (journal, volume, issue, pages 355–359, received 20 April 1937) was checked
  against Math-Net.Ru (`im3359`) and the scan itself. Math-Net.Ru's English page gives the German
  title of the summary, *Zur Statistik der Kristallisationsvorgänge in Metallen*.
