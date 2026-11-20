## Background

In 1940 N. K. Razumovsky collected data showing that the sizes of crushed particles (ores, gold
grains, sand) have logarithms that are close to normally distributed. Kolmogorov's short note
gives the explanation: a model of repeated random breakage in which this law appears as a limit
theorem.

## The model and the result

Particles break repeatedly. When a particle of size $r$ breaks, its fragments have sizes $kr$,
where the random ratios $k \in (0, 1]$ follow a law that **does not depend on $r$** (the
self-similarity hypothesis). Following one line of descent, after $n$ breaks the size is

$$r_n = r_0\, k_1 k_2 \cdots k_n, \qquad \log\frac{r_n}{r_0} = \log k_1 + \dots + \log k_n .$$

The logarithm is a sum of independent, identically distributed terms, so by the central limit
theorem

$$\frac{\log (r_n/r_0) - n m}{\sqrt n} \;\Longrightarrow\; \mathcal N(0, v), \qquad
m = \mathbb E \log k, \quad v = \operatorname{Var} \log k .$$

That is, sizes become asymptotically **log-normal**, with the mean of $\log r$ drifting down
linearly in $n$ and its variance growing linearly.

Kolmogorov's note works with the whole population: it follows the expected number of particles
smaller than a given size in a breakage process running in time, and proves that, normalized,
it tends to the normal law in the logarithmic variable. The lineage computation above is the
probabilistic heart of that argument.

## What the Lean file proves

| Result | Lean | Status |
|---|---|---|
| $\log r_n = \sum_i \log k_i$ | `log_size` | proved |
| $\mathbb E \log r_n = n\, \mathbb E \log k$ | `log_size_mean` | proved |
| $\operatorname{Var} \log r_n = n \operatorname{Var} \log k$ | `log_size_variance` | proved |
| $(\log r_n - nm)/\sqrt n \Rightarrow \mathcal N(0, v)$ | `lognormal_limit` | proved |
| population (expected-count) version | — | open |

The limit theorem uses Mathlib's central limit theorem. Sizes are measured in units of the
initial size ($r_0 = 1$), and the hypotheses are: ratios positive, independent, identically
distributed, with $\log k$ square-integrable.

## Legacy

The same mechanism (a quantity built from many independent multiplicative factors) is the basis
of Kolmogorov's 1962 refinement of his turbulence theory, where the energy dissipation averaged
over a ball is modelled as log-normal, and of later multiplicative cascade models of
intermittency.

## To check

- Whether an English translation appears in *Selected Works of A. N. Kolmogorov*, Vol. II.
- The note's own equation numbering, to cite in the Lean labels.
