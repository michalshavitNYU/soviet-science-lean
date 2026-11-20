## Background

In 1922 Friedmann showed that Einstein's field equations allow a closed world, of constant
positive spatial curvature, whose radius changes with time
([*Über die Krümmung des Raumes*](1922-friedmann-kruemmung-des-raumes.html), this dataset's
entry `1922-friedmann-kruemmung-des-raumes`). A space of positive constant curvature is naturally
finite, and the question of the finiteness of the universe was much discussed at the time. His
friend J. D. Tamarkin pointed out that the case of negative curvature needed its own
investigation. This seven-page note, written in Petersburg in November 1923, does it. Its answer
has two parts: the equations allow expanding worlds of negative curvature with positive density,
and so the equations alone cannot decide whether space is finite.

## The paper

**§1, the assumptions.** The field equations and the matter tensor are those of 1922, (A), (B),
(C). Space now has constant negative curvature $-1/R^2$, written in what is today called the
Poincaré half-space form,
$$ds^2 = \frac{R^2(dx_1^2 + dx_2^2 + dx_3^2)}{x_3^2} + M^2 dx_4^2, \qquad (\mathrm{D}')$$
with $R$ depending on time $x_4$ and $M$ on all four coordinates. The physical, indefinite form is
$$d\tau^2 = -\frac{R^2}{c^2}\,\frac{dx_1^2 + dx_2^2 + dx_3^2}{x_3^2} + M^2 dx_4^2. \qquad (\mathrm{D}'')$$
The mixed equations of (A) give $R'\,\partial M/\partial x_j = 0$, so either $R$ is constant
(a *stationary* world) or $M$ depends only on time (a *non-stationary* world).

**§2, nos. 1–2, stationary worlds.** Working with (D′), Friedmann integrates the equations for $M$:
$M = (P + Q)/x_3 + L$ (1), with $P$, $Q$ quadratic in $x_1$, $x_2$ (3). If $M$ really depends on
$x_1$ or $x_2$, equation (4) forces $\lambda R^2 = 3$ (printed $\lambda R^3 = 3$, (5)), and $L$
solves
$$\frac{\partial L}{\partial x_3} + \frac{L}{x_3} = 2n, \qquad (6)$$
so $L = L_0/x_3 + x_3$ for $n = 1$ (7) and $L = L_0/x_3$ for $n = 0$ (8). In both cases the
density is zero; the metrics are (D′₁), (D′₂). If $M$ depends only on $x_3$ and $x_4$, either
$\lambda R^2 = 3$ again (density zero), or $\lambda R^2 = 1$ and $M = M(x_4)$, a case pointed out
to him by V. A. Fock. Passing to (D″) with $M = 1$ this last case becomes
$$\lambda = -\frac{c^2}{R^2}, \qquad \varrho = -\frac{2}{\varkappa R^2}, \qquad (\mathrm{D}''_3)$$
with negative density. The conclusion: **a stationary world of constant negative curvature has zero
or negative density.** The physically possible static worlds are analogues of de Sitter's empty
world, not of Einstein's.

**§2, no. 3, non-stationary worlds.** With $M = 1$, (D′) gives
$$\frac{R'^2}{R^2} + \frac{2RR''}{R^2} + \frac{1}{R^2} - \lambda = 0, \qquad (9)$$
which is the 1922 equation (4) with $c = 1$, so "the whole discussion" of 1922 carries over.
Friedmann then writes the equation in the form (D″),
$$\frac{R'^2}{R^2} + \frac{2RR''}{R^2} - \frac{c^2}{R^2} - \lambda = 0,$$
integrates it once,
$$\frac{R'^2}{c^2} = \frac{A + R + \frac{\lambda}{3c^2}R^3}{R},$$
and finds the density $\varrho = 3A/(\varkappa R^3)$ (10), positive when $A > 0$. Compared with
1922 the only change is the sign of the curvature term: $+c^2/R^2$ becomes $-c^2/R^2$, and the
$-R$ in the first integral becomes $+R$. **Non-stationary worlds of negative curvature with
positive density exist.**

**§3, finiteness.** Whether a space is finite depends on which points one agrees to call
distinct: a sphere is finite, but regarded as an infinitely-many-sheeted surface it is not.
Friedmann proposes as one possible criterion the principle of "Phantomenangst" (fear of
phantoms): two distinct points are joined by only one geodesic, so that a light source cannot be
seen again as a "phantom" image at its own position. Under this principle spaces of positive
constant curvature are finite, but nothing follows for negative curvature. Hence Einstein's
equations, without further assumptions, cannot settle whether our world is finite.

## What the Lean file proves

All results in `SovietLean/HighEnergy/Friedmann1924.lean` are fully proved; nothing uses
`sorry`. The file imports the 1922 module and uses its equation (4) for `eq9_iff_eq4`.

| Paper | Lean | Status |
|---|---|---|
| (6): $L = L_0/x_3 + n x_3$ is a solution | `eq6_solution` | proved |
| (6): every solution on $x_3 > 0$ has this form | `eq6_general` | proved |
| (6) ⇒ (7) for $n = 1$; (6) ⇒ (8) for $n = 0$ | `eq7_of_eq6`, `eq8_of_eq6` | proved |
| (9) is the 1922 equation (4) with $c = 1$ | `eq9_iff_eq4` | proved |
| §2.3: $RR'^2 - c^2R - \frac{\lambda}{3}R^3$ has derivative $0$ along the (D″) equation | `energy_hasDerivAt` | proved |
| §2.3: the first integral, with $A = (RR'^2 - c^2R - \frac{\lambda}{3}R^3)/c^2$ | `eqA_of_eqR` | proved |
| §2.3: the converse, where $R' \ne 0$ | `eqR_of_eqA` | proved |
| (10): $\varrho = 3A/(\varkappa R^3)$ | `density_eq` | proved |
| (10): $\varrho > 0$ iff $A > 0$ (for $\varkappa > 0$, $R > 0$) | `density_pos_iff` | proved |
| (D″₃): constant $R$ solves the (D″) equation iff $\lambda = -c^2/R^2$ | `static_iff` | proved |
| (D″₃): $\varrho = -2/(\varkappa R^2)$ | `static_density` | proved |
| §2.2: the static (D″) world has $\varrho < 0$ | `static_density_neg` | proved |
| $\lambda \ge 0$, $A \ge 0$: $A + x + \frac{\lambda}{3c^2}x^3 > 0$ for $x > 0$ | `radicand_pos` | proved |
| ... so a positive solution is strictly monotone | `monotonic_world` | proved |
| $\lambda < 0$: the radicand is negative beyond $1 + (A + 2)/m$, $m = -\lambda/(3c^2)$ | `radicand_neg_of_large` | proved |
| $\lambda < 0$, $A > 0$: the radicand has a positive root | `exists_root_of_neg` | proved |
| $\lambda < 0$: every positive solution is bounded | `bounded_of_neg` | proved |
| $\lambda = 0$: the hyperbolic cycloid solves the first integral for $t \ne 0$ | `openWorld_eqA` | proved |
| ... $R = \frac{A}{2}(\cosh\eta - 1)$ at $t = \frac{A}{2c}(\sinh\eta - \eta)$ | `openWorld_param` | proved |
| ... $R(0) = 0$, $R$ strictly increasing for $t \ge 0$, $R \to \infty$ | `openWorld_zero`, `openWorld_strictMonoOn`, `openWorld_tendsto` | proved |
| (1)–(5): integrating the equations for $M$; $\lambda R^2 = 3$; $\varrho = 0$ for (D′₁), (D′₂) | — | open |
| periodicity of the world for $\lambda < 0$ | — | open |
| reduction of Einstein's equations to the equations for $R$ and $M$ | — | open |

How the formal statements match the paper.

- **Equations.** Mathlib has no Lorentzian geometry, so the equations for $R$ are taken as
  Friedmann prints them, as relations between the numbers $R$, $R'$, $R''$ at one time. The
  constants $c$, $\varkappa$, $\lambda$, $A$ are kept and nothing is rescaled. Lean reserves the
  letter `λ`, so the cosmological constant is called `lam`. The unnumbered (D″) equation and its
  integral are called `eqR` and `eqA` in the file.
- **The density equation.** To compute $\varrho$, Friedmann uses the equation (A) with
  $i = k = 4$, but he does not print it. The file uses
  $$\frac{3R'^2}{R^2} - \frac{3c^2}{R^2} - \lambda = \varkappa c^2 \varrho$$
  (`eq44`), which is the 1922 equation (5) with $c^2$ replaced by $-c^2$, as an explicit hypothesis.
  This is a reconstruction. As a check, it reproduces both densities that he does print:
  $-2/(\varkappa R^2)$ in (D″₃) and $3A/(\varkappa R^3)$ in (10).
- **Stationary worlds.** Only the ordinary differential equation (6) is formalized, with
  $x_4$ fixed: `eq6_general` shows that every differentiable solution on the half-space
  $x_3 > 0$ is $L_0/x_3 + n x_3$. The partial differential equations (2), the step from (4) to
  (5) and the "simple calculations" that give $\varrho = 0$ are not formalized. The negative
  density of the (D″₃) world is formalized (`static_density_neg`), given the (D″) equation and
  `eq44` with $R' = R'' = 0$.
- **Classification by $\lambda$.** Friedmann does not write it out; he says only that the
  discussion of 1922 carries over to (9). For the (D″) form the radicand is
  $A + x + \frac{\lambda}{3c^2}x^3$, so the 1922 analysis changes. For $\lambda \ge 0$ and
  $A \ge 0$ it has no positive root and every world is monotonic (`monotonic_world`); there is
  no analogue of the 1922 critical value $\lambda_1$ or of the periodic world for small positive
  $\lambda$. For $\lambda < 0$ it has a positive root and the radius is bounded (`bounded_of_neg`).
  These theorems record what the transfer gives; they are not statements printed in the paper.
- **The open world for $\lambda = 0$.** Friedmann gives no closed form. The first integral with
  $\lambda = 0$, $R'^2/c^2 = (A + R)/R$, is solved by the hyperbolic cycloid
  $$R = \frac{A}{2}(\cosh\eta - 1), \qquad t = \frac{A}{2c}(\sinh\eta - \eta),$$
  the analogue of the cycloid that the 1922 entry proves for the closed world. The file defines
  $R(t)$ by inverting $\eta \mapsto \sinh\eta - \eta$, which is strictly increasing by Mathlib's
  `Real.sinh_sub_id_strictMono`. At $t = 0$, $R = 0$ and the equation is singular; there the
  statement is only $R(0) = 0$.

## Remarks on the original

- **Eq. (3).** Printed $P = n x_1^2 + a_1 + b_1$, $Q = n x_2^2 + a_2 + b_2$. The general solution
  and (D′₁) have $a_1 x_1$ and $a_2 x_2$; the factors $x_1$, $x_2$ are missing in print.
- **Eq. (5).** Printed $\lambda R^3 = 3$. The factor $3 - \lambda R^2$ in (4) and case 1 on p. 330
  ("$\lambda R^2 = 3$") show that $\lambda R^2 = 3$ is meant.
- **(D′₂).** The first coefficient is printed $R/x_3^2$; by (D′) it should be $R^2/x_3^2$.
- **The (D″) equation for $R$.** The $c^2$ in $-c^2/R^2$ is damaged in the scan but legible.
- **"$x_4 = \varphi(x_4)$"** on p. 329 is printed so; on p. 330 the new coordinate is written
  $\overline{x}_4 = \varphi(x_4)$.
- **Sign of the curvature term.** In the form (D′) equation (9) has $+1/R^2$, like the 1922
  equation; in the form (D″) the sign is $-c^2/R^2$. Friedmann's remark that (9) "goes over
  exactly" into the 1922 equation (4) with $c = 1$ refers to the definite form (D′), where the
  substitution $R^2 \to -R^2/c^2$ that turns (D′) into (D″) has not yet been made.
- **Names.** The note is signed "A. Friedmann" (the 1922 paper "A. Friedman"). Tamarkine is
  J. D. Tamarkin; "Dr. W. Fock" is V. A. Fock.

## Legacy

The non-stationary negative-curvature worlds are the open ($k = -1$) Friedmann models. In modern
notation the first integral reads $\dot a^2/a^2 = \frac{8\pi G}{3}\varrho + \frac{c^2}{a^2} +
\frac{\Lambda c^2}{3}$, the $k = -1$ case of the Friedmann equation. With $\lambda = 0$ the open
dust universe expands forever, $R$ growing like $ct$ at late times. Friedmann's §3 is an early
statement that local geometry does not fix global topology: a hyperbolic space can be compact
after identifications, a point taken up in the later study of "cosmic topology".

## To check

- **Citation.** Volume 21, pages 326–332, the received date (7 January 1924) and the dating
  (St. Petersburg, November 1923) were read from the scan. Crossref (doi:10.1007/BF01328280)
  lists issue 1 and the publication date December 1924; the issue number and month were not
  checked against a bound volume.
- **The 1922 citation.** Friedmann cites his 1922 note as "Heft 6"; Crossref lists that paper as
  issue 1. Not resolved.
- **English translation.** The GRG 1999 translation is recorded from Crossref only; its text and
  numbering were not checked.
- **German translator.** Whether Friedmann wrote the German text himself or it was translated
  from Russian is not stated in the journal.
- **The density equation `eq44`.** It is reconstructed (see above), not read from the paper. A
  reader with the (D″) Christoffel symbols at hand should confirm it independently of the two
  printed densities.
- **Identification of Tamarkine and Fock** with J. D. Tamarkin and V. A. Fock is standard but
  not stated in the paper.
