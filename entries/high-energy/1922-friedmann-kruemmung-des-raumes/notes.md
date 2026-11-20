## Background

In 1917 Einstein applied general relativity to the universe as a whole. To get a static
universe filled with matter he added the cosmological term $\lambda g_{ik}$ to his equations and
found the "cylinder world": a closed space of constant positive curvature whose radius never
changes. De Sitter found a second static solution, empty of matter. Alexander Friedmann, a
mathematician and meteorologist in Petrograd, asked what happens if one keeps Einstein's
assumptions about matter and about the shape of space, but allows the radius of space to depend
on time. This ten-page note, his answer, contains the first expanding and oscillating
solutions of Einstein's equations.

Einstein first replied that the solutions were incompatible with the field equations
(Zeitschrift für Physik 11 (1922), 326) and then withdrew the objection, calling Friedmann's
results correct (Zeitschrift für Physik 16 (1923), 228). Both notes are in the same Internet
Archive item as the scan used here. Friedmann treated negative spatial curvature in a second
paper (Zeitschrift für Physik 21 (1924), 326–332).

## The paper

**§1, the assumptions.** The first class of assumptions is Einstein's: the field equations with
cosmological constant $\lambda$, (A), and incoherent matter at rest, so that $T_{44} = c^2\varrho
g_{44}$ is the only nonzero component, (C). The second class is geometric. Space has constant
curvature, which may depend on time, and time is orthogonal to space. Friedmann says that the
second assumption has no physical justification and only simplifies the calculation. The line
element is then (D), with a spatial radius $R(x_4)$ and a factor $M$ in front of $dx_4^2$.

**§2, no. 1, static worlds.** If $R$ does not depend on time, the remaining equations force
either $M = $ const, which is Einstein's cylinder world with
$$\lambda = \frac{c^2}{R^2}, \qquad \varrho = \frac{2}{\varkappa R^2}, \qquad
\overline{M} = \frac{4\pi^2}{\varkappa}R,$$
or $M \propto \cos x_1$, which is de Sitter's world with $\lambda = 3c^2/R^2$ and no matter.
So these are the only static worlds of this kind.

**§2, no. 2, the equations of a non-static world.** If $R$ depends on time, one may take
$M = 1$, and Einstein's equations reduce to two ordinary differential equations for $R(t)$:
$$\frac{R'^2}{R^2} + \frac{2RR''}{R^2} + \frac{c^2}{R^2} - \lambda = 0, \qquad (4)$$
$$\frac{3R'^2}{R^2} + \frac{3c^2}{R^2} - \lambda = \varkappa c^2 \varrho. \qquad (5)$$
Equation (4) has a first integral. Multiplying it by $R^2 R'$ gives the derivative of
$R R'^2 + c^2 R - \frac{\lambda}{3}R^3$, so this quantity is a constant, which Friedmann writes as
$c^2 A$:
$$\frac{1}{c^2}\Big(\frac{dR}{dt}\Big)^2 = \frac{A - R + \frac{\lambda}{3c^2}R^3}{R}. \qquad (6)$$
Today this is called the Friedmann equation. Substituting (6) into (5) gives the density,
$\varrho = 3A/(\varkappa R^3)$ (8), so $\varrho R^3$ is constant: matter is conserved. Since the
volume of space is $2\pi^2 R^3$, the total mass is $\overline{M} = 2\pi^2R^3\varrho$ and
$A = \varkappa\overline{M}/(6\pi^2)$ (9).

**§2, nos. 3–6, classification.** Separating variables in (6) gives $t$ as an integral of
$\sqrt{x/(A - x + \frac{\lambda}{3c^2}x^3)}$ (7). What $R$ can do depends on where the expression
under the root vanishes, that is on the positive roots of $A - x + \frac{\lambda}{3c^2}x^3$.
Writing $y = \lambda/(3c^2)$, these are the intersections with the curves $yx^3 - x + A = 0$
(10), which have a single maximum $y = 4/(27A^2)$ at $x = 3A/2$. This gives the critical value
$$\lambda_1 = \frac{4c^2}{9A^2}.$$

- $\lambda > \lambda_1$: no positive root. $R$ grows forever from $R = 0$: the *monotonic world
  of the first kind*. The "time since the creation of the world" is the time $R$ takes to grow
  from $0$ to its present value (12).
- $0 < \lambda < \lambda_1$, $R_0$ above the larger root $x_0'$: $R$ grows from $x_0'$, the
  *monotonic world of the second kind* (13).
- $\lambda < \lambda_1$, $R_0$ below the smallest root $x_0$: $R$ oscillates between $0$ and
  $x_0$, the *periodic world*, with world period $t_\pi$ (14). For small $\lambda$,
  $t_\pi \approx \pi A/c$ (15).

**§2, no. 7.** Friedmann says the data are too poor to decide which world is ours and that
$\lambda$ is not fixed by the theory. As an illustration, $\lambda = 0$ and a mass of
$5\cdot 10^{21}$ solar masses give a world period "of the order of 10 billion years".

## What the Lean file proves

All results in `SovietLean/HighEnergy/Friedmann1922.lean` are fully proved; nothing uses
`sorry`.

| Paper | Lean | Status |
|---|---|---|
| (4) ⇒ (6): $R R'^2 + c^2R - \frac{\lambda}{3}R^3$ has derivative $0$ along (4) | `energy_hasDerivAt` | proved |
| (4) ⇒ (6) on any time interval where $R \ne 0$ | `eq6_of_eq4` | proved |
| (6) ⇒ (4) at points where $R' \ne 0$ | `eq4_of_eq6` | proved |
| (5), (6) ⇒ (8): $\varrho = 3A/(\varkappa R^3)$ | `density_eq` | proved |
| volume of space $= 2\pi^2R^3$ (iterated integral over §1.4's coordinate ranges) | `volume_of_space` | proved |
| (8) ⇒ (9): $A = \varkappa\overline{M}/(6\pi^2)$ | `A_eq_mass` | proved |
| $A > 0$ iff $\overline{M} > 0$ (for $\varkappa > 0$) | `A_pos_iff` | proved |
| static world: (4) with $R' = R'' = 0$ iff $\lambda = c^2/R^2$ | `static_eq4_iff` | proved |
| Einstein's $\varrho = 2/(\varkappa R^2)$ | `static_density` | proved |
| Einstein's $\overline{M} = 4\pi^2R/\varkappa$ | `static_mass` | proved |
| (10): $(x - A)/x^3 \le 4/(27A^2)$ for $x > 0$ | `cubic_max` | proved |
| equality in (10) only at $x = 3A/2$ | `cubic_max_eq_iff` | proved |
| $\lambda > \lambda_1$: $A - x + \frac{\lambda}{3c^2}x^3 > 0$ for all $x > 0$ | `radicand_pos` | proved |
| $\lambda = \lambda_1$: $x = 3A/2$ is a root | `radicand_critical` | proved |
| $\lambda < 0$: a root $x_0 \in (0, A)$ exists | `exists_root_of_neg` | proved |
| $\lambda > \lambda_1$: a positive solution of (6) is strictly monotone | `monotonic_world` | proved |
| $\lambda = 0$: the cycloid $R(t)$ solves (6) wherever $R \ne 0$ | `periodicWorld_eq6` | proved |
| ... $R(0) = 0$, $R(\pi A/c) = 0$, $R(\pi A/(2c)) = A$ | `periodicWorld_zero`, `periodicWorld_period`, `periodicWorld_half` | proved |
| ... $R$ has period $\pi A/c$, as in (15) | `periodicWorld_periodic` | proved |
| ... $0 \le R \le A$ ($x_0 = A$ when $\lambda = 0$) | `periodicWorld_le` | proved |
| (7), (11)–(14) as integrals; root monotonicity in §2.3; periodicity for all $\lambda < 0$ | — | open |
| reduction of Einstein's equations (A)–(D₃) to (4), (5) | — | open |

How the formal statements match the paper.

- **Equations.** Mathlib has no Lorentzian geometry, so (4), (5), (6) are taken as Friedmann
  prints them, as relations between the numbers $R$, $R'$, $R''$ at one time. The constants
  $c$, $\varkappa$, $\lambda$, $A$ are kept and nothing is rescaled. Lean reserves the letter
  `λ`, so the cosmological constant is called `lam` in the code.
- **Derivatives.** $R'$ is the derivative of $R$ and $R''$ that of $R'$, stated with
  `HasDerivAt`. Divisions by $R$, $c$, $\varkappa$ in the paper become explicit hypotheses
  $R \ne 0$, $c \ne 0$, $\varkappa \ne 0$.
- **The first integral.** Friedmann obtains (6) "by integrating (4)". The Lean theorem proves
  this on a closed time interval where $R \ne 0$, with $A$ equal to
  $(R R'^2 + c^2R - \frac{\lambda}{3}R^3)/c^2$ at the left end. It does not need his remark
  "since $R' \ne 0$". That remark is needed for the converse, (6) ⇒ (4), which is proved
  separately.
- **Total mass.** The file defines $\overline{M} = 2\pi^2R^3\varrho$. That $2\pi^2R^3$ is the
  volume of space is proved separately: it is the integral of $R^3\sin^2x_1\sin x_2$ over
  Friedmann's ranges $x_1, x_2 \in (0, \pi)$, $x_3 \in (0, 2\pi)$ (§1.4). The step from the
  metric (D₃) to this volume element is not formalized.
- **Monotonic world.** `monotonic_world` proves the qualitative statement of §2.4: if
  $\lambda > \lambda_1$, a positive solution of (6) on a time interval has $R' \ne 0$, so $R$ is
  strictly monotone there. Which direction is a choice of the sign of time, as Friedmann notes.
- **Periodic world.** Friedmann gives no closed form. For $\lambda = 0$ the integral (7) can be
  done exactly, and the solution is a cycloid:
  $$R = \frac{A}{2}(1 - \cos\eta), \qquad t = \frac{A}{2c}(\eta - \sin\eta).$$
  The Lean file defines $R(t)$ by inverting $\eta \mapsto \eta - \sin\eta$ and proves that it
  solves (6) at every time with $R(t) \ne 0$. At the zeros, $R = 0$ and (6) is singular. The
  radius starts at $0$, reaches $A$ at $t = \pi A/(2c)$, returns to $0$ at $t = \pi A/c$ and
  repeats. So for $\lambda = 0$ the world period (15), $t_\pi = \pi A/c$, is exact, not just an
  approximation.

## Remarks on the original

- **Sign convention.** Friedmann's footnote to (B) says his signs of $R_{ik}$ and $\overline{R}$
  differ from the usual ones. This is why (A) has $-\varkappa T_{ik}$ on the right.
- **Eq. (5).** In the scan the first denominator is a damaged glyph that looks like $k^2$; it is
  $R^2$.
- **The figure.** The figure (p. 382) shows three curves of the family (10); the maximum
  $4/(27A^2)$ at $x = \frac32 A$ is marked on the middle one.
- **The numerical estimate.** With $\varkappa = 1.87\cdot10^{-27}$ CGS (his footnote, p. 379),
  $\overline{M} = 5\cdot10^{21}$ solar masses ($\approx 10^{55}$ g), (9) and (15) give
  $A \approx 3.1\cdot10^{26}$ cm and $t_\pi = \pi A/c \approx 3.3\cdot10^{16}$ s, about
  $10^{9}$ years. The paper says "of the order of 10 billion years". This entry's arithmetic
  gives one billion; see "To check".

## Legacy

Equation (6) is the Friedmann equation of modern cosmology for a closed universe filled with
dust: in today's notation, with scale factor $a = R$, $\dot a^2/a^2 = \frac{8\pi G}{3}\varrho -
\frac{c^2}{a^2} + \frac{\Lambda c^2}{3}$, where Friedmann's $\lambda$ is $\Lambda c^2$ and
his $\varkappa$ is $8\pi G/c^2$ (multiply (6) by $c^2/R^2$ and use (8)). Friedmann's periodic world with $\lambda = 0$ is the closed
"big bang – big crunch" model. Lemaître found the expanding solutions independently in 1927,
and Robertson and Walker later derived the metric (D₃) from symmetry assumptions alone, so the
models are known as Friedmann–Lemaître–Robertson–Walker (FLRW) cosmologies.

## To check

- **Citation.** Volume 10, pages 377–386, the received date (29 June 1922) and the dating
  (Petrograd, 29 May 1922) were read from the scan. Crossref (doi:10.1007/BF01332580) lists
  issue 1 and publication date December 1922. Friedmann's 1924 paper cites it as "Heft 6". The
  issue number was not checked against a bound volume.
- **Author's name.** The paper prints "A. Friedman"; the 1924 paper prints "A. Friedmann".
- **English translation.** The GRG 1999 translation is recorded from Crossref only; its text,
  and whether it reproduces the original numbering, were not checked.
- **Einstein's notes.** The references for Einstein's two notes (Z. Phys. 11 (1922), 326;
  Z. Phys. 16 (1923), 228) are taken from the Internet Archive item's description. The scans
  are in the item but were not read for this entry.
- **German translator.** The paper was written in Russian (Leiden's Ehrenfest archive holds the
  typed Russian manuscript); who translated it into German is not stated in the journal.
- **The 10-billion-year estimate.** Check whether the factor of ten between Friedmann's figure
  and the value from (9), (15) has been discussed in the historical literature, and what value
  of the solar mass he used.
- **The figure.** The values of $A$ for the three curves are not printed and were not
  measured.
