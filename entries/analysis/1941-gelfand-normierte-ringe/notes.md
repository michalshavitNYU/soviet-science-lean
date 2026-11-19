## What the Lean file proves

Let $A$ be a complex Banach algebra with unit $e$. Gelfand calls it a *normed ring*; his
rings are commutative, but the three Lean statements hold without commutativity.

1. **Nonempty spectrum.** For every $x \in A$ there is $\lambda \in \mathbb C$ such that
   $x - \lambda e$ has no inverse.
2. **Spectral radius formula.**
   $$\max_{\lambda \in \sigma(x)} |\lambda| = \lim_{n\to\infty} \|x^n\|^{1/n}.$$
   In Lean the left side is `spectralRadius ℂ x`, a supremum in $[0,\infty]$, and the limit
   is taken there too.
3. **Gelfand–Mazur.** If every nonzero element is invertible, then $A = \{\lambda e\}$.
   Lean states it as: each $x$ equals $z e$ for exactly one $z \in \mathbb C$.

All three proofs are Mathlib's. The Lean docstring explains how the formal hypotheses match the
paper's.

## Idea of the proofs

The key object is the resolvent $R(\lambda) = (x - \lambda e)^{-1}$. If the spectrum were
empty, $R$ would be a bounded entire function tending to $0$ as $|\lambda| \to \infty$, so
$R \equiv 0$ by Liouville's theorem, which is impossible. The spectral radius formula comes
from comparing the Laurent series $R(\lambda) = -\sum_n x^n \lambda^{-n-1}$ with the largest
disc on which $R$ is analytic. Gelfand–Mazur follows at once: pick $\lambda \in \sigma(x)$;
then $x - \lambda e$ is not invertible, so it is $0$.

## To check

- The theorem numbers in the paper, so the Lean labels can cite them.
- Whether an English translation exists (the paper is in German; Gelfand's *Collected Papers*,
  Springer, may reprint it).
