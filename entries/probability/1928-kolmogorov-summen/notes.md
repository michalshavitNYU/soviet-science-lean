## Open task

The Lean file states the maximal inequality

$$\mathbb P\Big(\max_{0\le k\le n} |S_k| \ge \varepsilon\Big) \le \frac{1}{\varepsilon^2}\sum_{i=0}^{n} \operatorname{Var} X_i$$

with `sorry` as its proof. A natural route: show $S_k^2$ is a submartingale for the
natural filtration, then apply Doob's maximal inequality `MeasureTheory.maximal_ineq`
and $\mathbb E[S_n^2] = \sum_i \operatorname{Var} X_i$.

To check: whether an English translation appears in *Selected Works of A. N. Kolmogorov*, Vol. II.
