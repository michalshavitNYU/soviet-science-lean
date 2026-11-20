## Background

Andrei Andreevich Markov (1856–1922), of St Petersburg, was a student of Chebyshev. In 1902
P. A. Nekrasov, of the Moscow school, had argued that the law of large numbers needs the
quantities to be independent. This paper is Markov's answer. It ends: "Thus the independence of
the quantities is not a necessary condition for the existence of the law of large numbers."

To show this, Markov introduced sequences in which each quantity depends only on the one before
it. These are now called Markov chains, and this paper is where they first appear. A footnote in
§3 points to his 1907 paper "Investigation of a remarkable case of dependent trials", where he
continued the subject.

## What the paper does

The starting point is Chebyshev's proof. Write $a_i$ for the expectation of $x_i$ and
$z_i = x_i - a_i$. Then
$P\big(|\tfrac{1}{n}\sum x_i - \tfrac{1}{n}\sum a_i| \ge \varepsilon\big) \le
E(z_1 + \cdots + z_n)^2 / (n^2\varepsilon^2)$. So the law of large numbers holds whenever
$E(z_1 + \cdots + z_n)^2$ grows more slowly than $n^2$, whether or not the $x_i$ are independent.
Markov expands
$$(z_1 + \cdots + z_n)^2 = \sum z_k^2 + 2z_1z_2 + 2(z_1 + z_2)z_3 + \cdots$$
and controls the cross terms in three situations.

1. **§1: negative correlation.** Suppose that when one quantity is larger, the expectations of
   the others are smaller. Then each $E z_l z_k$ is negative. Markov gets the sign from an
   inequality of Chebyshev: if one sequence increases while another decreases, the weighted mean
   of their product is at most the product of their weighted means. Hence
   $E(\sum z_k)^2 < \sum E z_k^2$. His example is an urn from which balls are drawn without
   replacement and topped up halfway through.
2. **§2: the first Markov chain.** The event $A$ is observed at a series of trials. Its
   probability at a trial is $p'$ if $A$ occurred at the immediately preceding trial and $p''$
   if not, whatever happened earlier. With no information, the probability is $p$ at every
   trial, and $p = pp' + qp''$ with $q = 1 - p$. Markov computes the probability $R_m$ of $A$ at
   trial $l + m$, given $A$ at trial $l$. It satisfies $R_{m+1} = p'' + (p' - p'')R_m$, so
   $$R_m = p + q(p' - p'')^m, \qquad E z_l z_k = pq\,(p' - p'')^{k-l}.$$
   Summing the geometric series gives $E(\sum z_k)^2 < npq$ if $p' < p''$, and
   $E(\sum z_k)^2 < npq\,(1 + p' - p'')/(1 - p' + p'')$ if $p' > p''$. Either way, the frequency
   of $A$ tends to $p$ in probability.
3. **§3: a generating function.** Let $P_{m,k}$ be the probability of exactly $m$ occurrences in
   $k$ trials, and $\Omega_k = \sum_m P_{m,k}\xi^m$. Splitting by the result of the last trial
   gives a pair of first-order recurrences. Eliminating one function gives
   $\Omega_{k+1} - (p'\xi + q'')\Omega_k + (p' - p'')\xi\,\Omega_{k-1} = 0$, so $\Omega_k$ is
   the coefficient of $t^k$ in
   $$\frac{1 + (p'' - p')(q\xi + p)t}{1 - (p'\xi + q'')t + (p' - p'')\xi t^2}.$$
4. **§4: a counterexample.** In an urn where each ball drawn is put back together with another
   of the same colour (now called Pólya's urn), more white balls drawn make the next white ball
   more likely. The correlations are positive and
   $E(m - \tfrac{na}{a+b})^2 = \tfrac{nab(n+a+b)}{(a+b)^2(a+b+1)}$, which grows like $n^2$. So
   the law of large numbers fails: the frequency $m/n$ does not settle near any fixed number.
   For $a = b = 1$ every count $m = 0, \ldots, n$ has probability $1/(n+1)$.
5. **§5: general chains.** The quantity $x_{k+1}$ depends only on $x_k$, through transition
   probabilities $p_{\alpha,\gamma}$, all positive. Let $A^{(i)}_\alpha$ be the expectation of
   $x_{k+i}$ given $x_k = \alpha$. Then $A^{(i)}_\alpha = \sum_\gamma p_{\alpha,\gamma}
   A^{(i-1)}_\gamma$. Each new set of values therefore lies within the range of the previous one.
   Markov's key step is that the range shrinks by a fixed factor: write
   $A^{(i)}_\alpha - A^{(i)}_\beta = \sum_\gamma (p_{\alpha,\gamma} - p_{\beta,\gamma})
   A^{(i-1)}_\gamma$. The coefficients sum to zero, and their positive parts sum to some
   $h < 1$, because all the $p$'s are positive. So the spread $\Delta^{(i)}$ satisfies
   $\Delta^{(i)} < H\Delta^{(i-1)}$ with $H < 1$. All the $A^{(i)}_\alpha$ therefore tend to a
   common limit $a$, geometrically fast. This makes the correlations decay geometrically. As in
   §2, $E(\sum z_k)^2 < Gn$, and the mean of $x_1, \ldots, x_n$ tends to $a$ in probability. In
   modern terms $h$ is the Dobrushin ergodic coefficient, and the argument is the standard
   proof that a positive stochastic matrix contracts.

## What the Lean file proves

Every listed result is proved; there is no `sorry`.

| Paper | Lean | Status |
|---|---|---|
| Introduction: $E(\sum z_i)^2/n^2 \to 0$ implies the law of large numbers | `chebyshev_principle` | proved |
| p. 138: the expansion of $(z_1 + \cdots + z_n)^2$ | `sq_sum_eq` | proved |
| p. 138: Chebyshev's inequality for oppositely ordered sequences | `chebyshev_sum_le` | proved |
| §1: nonpositive $E z_l z_k$ and bounded $E z_k^2$ imply the law of large numbers | `lln_of_cov_nonpos` | proved |
| §5 (p. 155), also §2: $\lvert E z_l z_k\rvert \le D H^{k-l}$ implies $E(\sum z_k)^2 \le Gn$ and the law of large numbers | `lln_of_cov_decay` | proved |
| §2, p. 140: $p = pp' + qp''$ | `IsSimpleChain.stationary` | proved |
| §2, p. 141: $R_m = p + q(p' - p'')^m$ | `R_eq` | proved |
| §2, p. 141: $P(A$ at trials $l$ and $l + m) = pR_m$ | `IsSimpleChain.prob_both` | proved |
| §2, p. 142: $E z_l z_{l+m} = pq(p' - p'')^m$ | `IsSimpleChain.cov_eq` | proved |
| §2, p. 142: $E(\sum z_k)^2 \le npq$ if $p' \le p''$ | `IsSimpleChain.second_moment_le_of_nonpos` | proved |
| §2, p. 142: $E(\sum z_k)^2 \le npq(1 + p' - p'')/(1 - p' + p'')$ if $p' \ge p''$ | `IsSimpleChain.second_moment_le_of_nonneg` | proved |
| §2: the frequency of $A$ tends to $p$ in probability | `IsSimpleChain.lln` | proved |
| §3, p. 144: the recurrence for $\Omega_k$ | `Omega_recurrence` | proved |
| §3, p. 145: $B = (p'' - p')(q\xi + p)$ | `numerator_B` | proved |
| §5, p. 152: $A^{(i)}$ lies between the extremes of $A^{(i-1)}$ | `T_mem` | proved |
| §5, p. 153: $A^{(i)}_\alpha - A^{(i)}_\beta \le h\,\Delta^{(i-1)}$ | `T_sub_le` | proved |
| §5, p. 153: $h < 1$ | `h_lt_one` | proved |
| §5, p. 154: $\Delta^{(i)} \le H^i \Delta^{(0)}$ | `iterate_spread` | proved |
| §5, p. 154: one common limit, within $CH^i$ | `iterate_tendsto` | proved |
| §5, p. 152: $a_{k+i} = \sum_\alpha p^{(k)}_\alpha A^{(i)}_\alpha$ | `IsChain.integral_eq_sum_iterate` | proved |
| §5, p. 155: $\lvert E z_l z_{l+i}\rvert \le D H^i$ | `IsChain.abs_cov_le` | proved |
| §5: the law of large numbers for a chain | `IsChain.lln` | proved |

How the formal statements match the paper:

- **Probability.** "Mathematical expectation" is the integral against a probability measure.
  "With probability as close to certainty as one wishes, the mean differs from $a$ by less than
  any given quantity" is convergence in probability: for every $\varepsilon > 0$,
  $P(|\tfrac{1}{n}\sum_{i<n} x_i - a| \ge \varepsilon) \to 0$. Trials are numbered from $0$, not
  $1$.
- **Chebyshev's principle** has exactly the hypothesis of the introduction: the expectation of
  the square of $\sum x_i - \sum a_i$, divided by $n^2$, tends to zero. The $x_i$ are assumed
  square integrable, which the paper takes for granted.
- **The general criteria.** The paper compares the mean of the $x_i$ with the mean of their
  expectations, and in §5 with the limit $a$ of the $a_k$. The formal criteria
  (`lln_of_cov_nonpos`, `lln_of_cov_decay`) assume that the $a_k$ converge to some $a$ and
  conclude that the mean tends to $a$; this covers both. "The expectation of the square remains
  finite" is read as a uniform bound.
- **§1.** We prove Chebyshev's inequality (with weights) and, separately, that nonpositive
  correlations give the law of large numbers. We do not formalize the step from "a larger $x_l$
  lowers the conditional expectation of $x_k$" to "$E z_l z_k < 0$" for general random
  variables, nor the two urn examples.
- **§2.** The structure `IsSimpleChain` records the hypotheses. `X k` is $1$ or $0$ as $A$ occurs
  at trial $k$ or not, and $P(X_k = 1) = p$ for every $k$. For every event $E$ determined by
  trials $0, \ldots, k$:
  $P(E,\ X_k = 1,\ X_{k+1} = 1) = p'\,P(E,\ X_k = 1)$, and
  $P(E,\ X_k = 0,\ X_{k+1} = 1) = p''\,P(E,\ X_k = 0)$. This is the paper's "whatever the
  results of the other preceding trials". The relation $p = pp' + qp''$ is derived, not
  assumed. The paper's $R_m$ is defined by its recurrence with $R_0 = 1$ (the value $R_1 = p'$ is
  `R_one`). The law of large numbers assumes $|p' - p''| < 1$. The paper uses this tacitly when
  it divides by $1 - p' + p''$; it rules out the chains that never change state or always do.
- **§3.** Only the algebra is formalized: the elimination giving the second-order recurrence
  (stated over any commutative ring, for any $\Phi, \Psi$ satisfying the paper's first-order
  recurrences), and the simplification of $B$. The recurrences for $U_{m,k}$, $V_{m,k}$ are not
  derived from the chain, and the power-series identity is not stated as such.
- **§5.** The structure `IsChain` records the hypotheses. The quantities take finitely many
  values, labelled by a finite type `S` (the paper's $\alpha, \beta, \gamma, \ldots$), and the
  numerical value of the label is `v`. The paper uses the same letter for both. For every event
  $E$ determined by $x_0, \ldots, x_k$:
  $P(E,\ x_k = \alpha,\ x_{k+1} = \gamma) = p_{\alpha,\gamma}\,P(E,\ x_k = \alpha)$, with
  $p_{\alpha,\gamma}$ independent of $k$, as the paper assumes. The initial law is arbitrary.
  The transition probabilities are assumed positive with rows summing to $1$, as in the paper.
  The paper's $A^{(i)}_\alpha$ is `(T P)^[i] v α`, and its constant $C$ is $M - m$ for any bounds
  $m \le v \le M$. The paper's $D$ becomes $(M - m)^2$ and its $G$ becomes
  $D(1 + 2H/(1 - H))$.
- **Finitely many values.** The paper writes "$\alpha, \beta, \gamma, \ldots$" without saying
  the list is finite. Its argument needs a constant $H < 1$ bounding every $h$, which is
  automatic only for finitely many values; we assume finitely many.
- **Inequalities.** The paper's strict inequalities are proved as non-strict ones.
- **Proofs.** The proofs follow the paper. The main difference is in §5: the existence of the
  common limit $a$ is proved by showing the $A^{(i)}$ form a Cauchy sequence, which the paper
  treats as evident from $\Delta^{(i)} < CH^i$. Chebyshev's inequality is applied through
  Mathlib's `mul_meas_ge_le_integral_of_nonneg`.

## Remarks on the text

- **Dates.** The issue's cover says 1906, but §4 ends with the date 16 January 1907 and the
  paper with 25 March 1907. The same issue contains the minutes of the Society's meeting of
  23 December 1906. So the paper was finished and printed in 1907 in a volume dated 1906; it is
  usually cited as 1906.
- **"Under the condition that" (§3).** $U_{m,k}$ and $V_{m,k}$ are described as "the same
  probability as $P_{m,k}$, but under the condition that" $A$ does or does not occur at the last
  trial. The recurrences and $P_{m,k} = U_{m,k} + V_{m,k}$ show that these are joint
  probabilities (exactly $m$ occurrences *and* the last trial has the stated result), not
  conditional ones.
- **Notation.** $R^l_k$ (p. 141) is a probability, not a power. On p. 138 the index $(i)$ is
  printed above each letter in the sums.

## Errata in the original

- **p. 138.** "provided only that the mathematical expectation $z_n$ remains finite": the square
  $z_n^2$ is meant.
- **p. 142.** In the bound for $p' > p''$ the second "$<$" is an equality:
  $1 + \frac{2(p' - p'')}{1 - p' + p''} = \frac{1 + p' - p''}{1 - p' + p''}$.
- **p. 148.** For $\mu$ to be the most probable value, the second inequality must read
  $(a-1)n + a - 1 \ge (a+b-2)\mu$. In the scanned copy the sign is partly overwritten by hand, so
  what was printed is unclear.
- **Handwriting in the scan.** On p. 142 the last exponent in the sum is overwritten by hand with
  a "1" (the correct exponent is $k - 1$). On p. 140 a reader wrote $z_l = x_l - a_l$ in the
  margin. These marks belong to the scanned copy, not to the printed text.

## To check

- **Citation.** Series 2, vol. 15, no. 4, pp. 135–156, issue dated 1906: checked on the scan
  (cover and printed page numbers). Many sources cite the volume as "15 (94)"; that alternative
  numbering was not checked.
- **Howard's translation.** Several sources say an English translation appears in
  R. A. Howard, *Dynamic Probabilistic Systems*, vol. 1 (Wiley, 1971), Appendix B. This was not
  verified, so it is not listed under `existing_translations`.
- **The 2006 reprint** in the *Journal Électronique d'Histoire des Probabilités et de la
  Statistique* 2(1b), article 10, is confirmed by its EuDML record. The record does not say whose
  translation it reprints, and the reprint was not read.
- **Selected works.** The paper is said to be reprinted in Markov's *Izbrannye trudy* (Moscow,
  1951). This was not checked.
- **Nekrasov.** The background (Nekrasov's 1902 claim) comes from secondary literature (Seneta's
  historical articles). It was not checked against Nekrasov's papers, and the 1906 paper itself
  does not mention Nekrasov.
- **Footnote references.** The references in the footnotes were transcribed from the scan but
  not looked up: Chebyshev, *Works* vol. I ("On mean values") and vol. II, pp. 716–719; Korkine,
  *Comptes Rendus* t. XCVI; Markov, *Izvestiya Akad. Nauk* 1907.
- **The urn examples.** The claims of §1 (urn without replacement, topped up) and §4 (variance
  formula, mode, the case $a = b = 1$) were not checked independently.
