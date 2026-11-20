## About the translation

The translation follows the original's equation numbering, so the Lean labels and these notes
can cite equations by number. The final part of the paper (from the Friedmann–Keller chain to
the end, p. 312) and equations (25)–(28) were drafted with AI assistance from the scanned
original and are awaiting a check against it.

## The setting

Obukhov looks for the common structure of two classical systems: the Euler equations of an
ideal incompressible fluid and Euler's equations for a free rigid body. Both are quadratic in
the unknowns and both conserve a positive quadratic energy. He calls a system
$\dot u^i = \Gamma^i_{\lambda\mu} u^\lambda u^\mu$ on $\mathbb R^n$ a **system of hydrodynamic
type** when

1. $\Gamma^i_{jk} = \Gamma^i_{kj}$ (this costs nothing: only the symmetric part enters);
2. phase volume is preserved, which for a quadratic field means $V_j = \Gamma^\lambda_{j\lambda} = 0$;
3. the energy $2E = g_{\mu\nu}u^\mu u^\nu$ is conserved, which follows from the cyclic identity
   $\Gamma_{i,jk} + \Gamma_{j,ki} + \Gamma_{k,ij} = 0$.

Galerkin truncations of ideal hydrodynamics in a periodic box are examples, as T. D. Lee
observed in 1952, and so are the finite-difference schemes used in numerical weather forecasting.

## Why it matters for turbulence

Because volume is preserved, the phase density obeys the Liouville equation, and any function
of the integrals of motion is a stationary density. Energy alone gives the Boltzmann (Gaussian,
"white-noise") distribution. A *non-trivial* stationary Gaussian requires a second quadratic
integral, and Obukhov argues these are exceptional. He gives two examples:

- **$n = 3$:** every such system is equivalent to the free rigid body. In canonical form
  $\dot u_1 = p u_2 u_3$, $\dot u_2 = q u_3 u_1$, $\dot u_3 = r u_1 u_2$ with $p + q + r = 0$,
  and the second integral is $I = (q-r)u_1^2 + (r-p)u_2^2 + (p-q)u_3^2$.
- **Two-dimensional ideal flow:** energy and enstrophy are both conserved, which gives a
  two-parameter family of Gaussian measures. In the Laplacian eigenbasis the modal variances
  have the form $C^2 / [k^2(1 + L_0^2 k^2)]$, with $C$ an intensity and $L_0$ a length scale of
  the "two-dimensional turbulence". These are the absolute equilibria that Kraichnan (1967) had
  also used for two-dimensional turbulence.

The paper ends with the **Friedmann–Keller moment chain** for these systems: the equations
linking the second moments $B^{ij} = \langle u^i u^j\rangle$ to the third moments, and the
third moments to the fourth. Close the chain with **Millionshchikov's hypothesis**, which
expresses fourth moments through second moments as for a Gaussian. Obukhov states that any
stationary solution of the closed system is then an *exact* Gaussian solution of the whole chain.
All odd moments vanish, and the quadratic form built from the inverse of $B$ is an exact
integral of motion. So again, non-trivial solutions need a second quadratic integral besides
the energy.

He also counts the free parameters: for a fixed energy form, $\Gamma$ has
$N = n(n+2)(n-2)/3$ independent components, so $N = 5$ when $n = 3$.

## What the Lean file proves

All statements are in Obukhov's "Cartesian" coordinates $g_{ik} = \delta_{ik}$.

| Paper | Lean | Status |
|---|---|---|
| cyclic identity ⇒ energy conserved | `energy_identity`, `energy_conserved` | proved |
| volume preservation ⇔ $V_j = 0$ | `divergence_free_iff` | proved |
| Boltzmann distribution is stationary | `boltzmann_stationary` | proved |
| canonical $n=3$ form is admissible iff $p+q+r=0$ | `canonical_cyclic` | proved |
| $E$ and $I$ conserved for $n = 3$ | `rigid_body_integrals` | proved |
| $N = n(n+2)(n-2)/3$ for $n \ge 2$ | `finrank_shtSpace` | proved |
| Millionshchikov closure ⇒ exact Gaussian, second integral | — | not yet stated |

## Notes on the source

- **Factor of 2.** With a symmetric $\Gamma$, $\dot u^1 = 2\Gamma_{1,23}u^2u^3$, so the canonical
  equations $\dot u_1 = p u_2 u_3$ correspond to $\Gamma_{1,23} = p/2$, not $p$. This is a
  normalization and does not affect $p + q + r = 0$.
- **$n = 1$.** The formula for $N$ gives $-1$, but the space is $\{0\}$; the count holds for
  $n \ge 2$.

## How the count is proved

Tensors $\Gamma_{i,jk}$ symmetric in $j,k$ form a space of dimension $n\binom{n+1}{2}$. The cyclic
sum $\Gamma_{i,jk}+\Gamma_{j,ki}+\Gamma_{k,ij}$ of such a tensor is *totally* symmetric, and every
totally symmetric $T$ arises (from $\Gamma = T/3$). So the cyclic sum maps onto a space of
dimension $\binom{n+2}{3}$, the number of multisets of size 3. The trace $V_j$ then maps onto
$\mathbb R^n$: for each $j$, pick $l \ne j$ (this is where $n \ge 2$ is needed) and take
$\Gamma_{l,jl}=\Gamma_{l,lj}=1$, $\Gamma_{j,ll}=-2$, which has zero cyclic sum and trace $e_j$.
Rank–nullity gives
$$N = n\binom{n+1}{2} - \binom{n+2}{3} - n = \frac{n(n+2)(n-2)}{3}.$$
- **The second integral needs nothing.** $I$ is conserved for *any* $p, q, r$:
  $(q-r)p + (r-p)q + (p-q)r = 0$ identically. The condition $p + q + r = 0$ is needed only for
  the energy.
- **A slip in the original.** The paper says the symmetry condition (5) is easy to check in the periodic
  case via Fourier modes. The argument given, that each $\Gamma^j_{ij}$ vanishes, actually proves
  the volume condition (7).
