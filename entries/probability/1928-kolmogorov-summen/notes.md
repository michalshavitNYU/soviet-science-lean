## The result

Let $X_0, \dots, X_n$ be independent random variables with mean zero and finite variance, and
let $S_k = X_0 + \dots + X_k$. Then for every $\varepsilon > 0$

$$\mathbb P\Big(\max_{0\le k\le n} |S_k| \ge \varepsilon\Big) \le \frac{1}{\varepsilon^2}\sum_{i=0}^{n} \operatorname{Var} X_i .$$

Chebyshev's inequality gives the same bound for the single event $|S_n| \ge \varepsilon$.
Kolmogorov's point is that the bound holds for the whole path $S_0, \dots, S_n$ at no extra
cost. This is what makes it useful for proving almost-sure convergence of random series.

## How the Lean proof goes

Kolmogorov's own argument splits the event according to the first time $k$ at which
$|S_k| \ge \varepsilon$. The Lean proof packages the same idea through martingale theory, which
Mathlib already has.

1. **$S_k^2$ is a submartingale** for the filtration $\mathcal G_k = \sigma(X_0,\dots,X_k)$.
   For $i \le j$ and an event $s \in \mathcal G_i$, write $S_j = S_i + R$ with
   $R = X_{i+1} + \dots + X_j$:
   $$\int_s S_j^2 = \int_s S_i^2 + 2\,\mathbb E[\mathbf 1_s S_i \cdot R] + \int_s R^2 .$$
   The middle term vanishes, because $\mathbf 1_s S_i$ depends only on $X_0,\dots,X_i$, $R$ only on
   $X_{i+1},\dots,X_j$, and $\mathbb E R = 0$. The last term is nonnegative.
2. **Doob's maximal inequality** (`MeasureTheory.maximal_ineq`) then gives
   $\varepsilon^2\, \mathbb P(\max_k S_k^2 \ge \varepsilon^2) \le \mathbb E[S_n^2]$.
3. **$\mathbb E[S_n^2] = \sum_i \operatorname{Var} X_i$**, by independence and mean zero.

The Lean statement assumes the $X_i$ are measurable functions, the standard setting. Doob's
theorem needs this; almost-everywhere measurability is not enough.

## To check

- Where exactly in the paper the inequality is stated (section, page, numbering).
- Whether an English translation appears in *Selected Works of A. N. Kolmogorov*, Vol. II.
