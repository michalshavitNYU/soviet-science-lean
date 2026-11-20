## Background

In 1937 R. A. Fisher, in England, and Kolmogorov, Petrovsky and Piskunov, in Moscow, independently
asked how fast an advantageous gene spreads through a population living along a line. Let
$u(x, t) \in [0, 1]$ be the local concentration of the gene. Individuals move about at random,
which spreads $u$ by diffusion, and selection makes $u$ grow where the gene is present but not yet
universal. This gives

$$\frac{\partial u}{\partial t} = D \frac{\partial^2 u}{\partial x^2} + F(u), \qquad
F(0) = F(1) = 0, \qquad F'(0) = \alpha > 0,$$

with $F$ positive between $0$ and $1$. Fisher's example is $F(u) = \alpha u(1 - u)$. The Moscow
paper treats a general $F$ of this kind and proves, rather than conjectures, what happens.

## The result, in outline

Start with the gene present on one side of a point and absent on the other. The solution
develops into a front that moves into the empty region, and its speed tends to

$$c_* = 2\sqrt{\alpha D}.$$

This is the smallest speed at which a travelling front $u = U(x - ct)$ exists. Fronts of every
speed $c \ge 2\sqrt{\alpha D}$ exist, but the step initial state picks out the slowest one.

Why $2\sqrt{\alpha D}$? Far ahead of the front $u$ is small, so $F(u) \approx \alpha u$ and the
equation is close to its linearization $u_t = D u_{xx} + \alpha u$. An exponential tail
$e^{-\mu(x - ct)}$ solves the linearization exactly when

$$c = D\mu + \frac{\alpha}{\mu}.$$

As $\mu$ ranges over $(0, \infty)$ this speed is never below $2\sqrt{\alpha D}$, and it reaches
that value at $\mu = \sqrt{\alpha / D}$. Equivalently, the profile equation near $U = 0$,
$D U'' + c U' + \alpha U = 0$, has real exponential solutions only when $c^2 \ge 4 \alpha D$;
for slower speeds its solutions oscillate, so the profile would take negative values, which a
concentration cannot do.

The hard part of the paper, which this entry does not formalize, is the nonlinear analysis:
the phase-plane argument that fronts exist, and the comparison argument that the solution from
step data converges to the front of minimal speed.

## What the Lean file proves

All results in `SovietLean/Analysis/KPP1937.lean` are fully proved; nothing uses `sorry`.

| Result | Lean | Status |
|---|---|---|
| $e^{-\mu(x-ct)}$ ($\mu > 0$) solves $u_t = D u_{xx} + \alpha u$ iff $c = D\mu + \alpha/\mu$ | `linear_exp_solves_iff` | proved |
| $D\mu + \alpha/\mu \ge 2\sqrt{\alpha D}$ for $\mu > 0$ ($\alpha, D > 0$) | `two_sqrt_le_speed` | proved |
| equality at $\mu = \sqrt{\alpha/D}$ | `speed_at_optimum` | proved |
| $2\sqrt{\alpha D}$ is the least speed of such an exponential solution | `minSpeed_isLeast` | proved |
| no such solution with $c < 2\sqrt{\alpha D}$ | `no_slow_exponential` | proved |
| $u = U(x - ct)$ solves the equation iff $D U'' + c U' + F(U) = 0$ | `travelling_wave_iff` | proved |
| $e^{-\mu\xi}$ solves $D U'' + c U' + \alpha U = 0$ iff $D\mu^2 - c\mu + \alpha = 0$ | `exp_profile_iff` | proved |
| a real rate $\mu$ exists iff $c^2 \ge 4\alpha D$ | `exists_real_rate_iff` | proved |
| for $c \ge 0$: $c^2 \ge 4\alpha D$ iff $c \ge 2\sqrt{\alpha D}$ | `sq_ge_iff_ge_two_sqrt` | proved |
| existence of fronts for $c \ge 2\sqrt{\alpha D}$ | — | open |
| convergence of step data to the minimal-speed front | — | open |

How the formal statements are set up. Partial derivatives are taken along coordinate lines:
$u_t$ at $(x, t)$ is the derivative of $s \mapsto u(x, s)$ at $t$, and $u_{xx}$ is the second
derivative of $y \mapsto u(y, t)$ at $x$. The constants $D$ and $\alpha$ are kept general rather
than scaled to $1$. The equation is checked at a single point $(x, t)$; for the exponentials this
is no restriction, since the condition on $c$ does not depend on the point.

## Translations

English translations are cited in two places (see `existing_translations` in `meta.yaml`):
*Selected Works of A. N. Kolmogorov*, Vol. I (Kluwer, 1991), translated by V. M. Volosov, and
P. Pelcé (ed.), *Dynamics of Curved Fronts* (Academic Press, 1988). Both are known here only from
citations in other works. No translation is hosted, because the paper is in copyright.

## To check

- **Page range.** zbMATH (Zbl 0018.32106) gives pages 1–25; some Russian bibliographies of
  Kolmogorov's works give 1–26. Check against the journal.
- **Journal name.** zbMATH abbreviates it as *Bull. Univ. État Moscou, Sér. Int., Sect. A:
  Math. et Mécan.* 1, Fasc. 6; the full French form used in `source` is expanded from that.
- **Existing translations.** The page numbers 248–270 (Selected Works I) and 105–130 (Pelcé)
  come from secondary citations (Wikipedia; a 2004 arXiv paper) and were not checked in the books.
- **The paper's own numbering and hypotheses.** The original French text was not available to
  the contributor, so the Lean labels describe the results rather than cite the paper's
  sections or equations, and the exact hypotheses the paper puts on $F$ (beyond
  $F(0) = F(1) = 0$, $F'(0) = \alpha > 0$) are not recorded here.
