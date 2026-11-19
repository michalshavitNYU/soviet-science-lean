## What the Lean file proves

Kolmogorov states the law for events determined by a sequence of independent random
variables that do not depend on any finite number of them. In Lean, "does not depend on
finitely many terms" becomes measurability with respect to the **tail σ-algebra**
$\bigcap_n \bigvee_{i \ge n} \sigma(x_i)$.

Two forms are given:

1. for an independent sequence of σ-algebras $s_i$ (the general form);
2. for independent real random variables $x_i$, by taking $s_i = \sigma(x_i)$.

The proof is Mathlib's; this entry records that the library statement matches the source.

## Terminology

| German (1933) | English (Morrison 1950) | Lean / Mathlib |
|---|---|---|
| Wahrscheinlichkeitsfeld | probability field | `MeasureSpace`, `IsProbabilityMeasure` |
| unabhängig | independent | `iIndep`, `iIndepFun` |
