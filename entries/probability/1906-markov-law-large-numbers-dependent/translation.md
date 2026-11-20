<!-- AI-drafted translation from the Russian; section numbers and page numbers follow the original. -->

*Translated from the Russian original in* Izvestiya Fiziko-matematicheskago obshchestva pri
Imperatorskom Kazanskom universitete *(Bulletin de la Société physico-mathématique de Kasan),
2nd series, vol. 15, no. 4 (1906), pp. 135–156, read from the page images of the scan in the
[St Petersburg University repository](http://hdl.handle.net/11701/36473) (file `Kazan_1906.pdf`,
PDF pages 5–26). Draft translation by Claude (AI), not yet checked by a second reader. The
printed page numbers are given as [p. 136] etc. The paper has no numbered equations.
Misprints and handwritten marks in the scanned copy are kept as printed and flagged in
[square-bracketed translator's notes]. "Матем. ожид." (mathematical expectation) is rendered
"math. expect.", and "числ. знач." (numerical value) as "num. val.", as in the original.*

---

## Extension of the law of large numbers to quantities depending on each other

The law of large numbers, by virtue of which one can assert, with a probability as close to
certainty as one wishes, that the arithmetic mean of several quantities, when the number of
these quantities is sufficiently large, will differ arbitrarily little from the arithmetic mean
of their mathematical expectations, was derived by Chebyshev\*) from a consideration of the
mathematical expectation of the square of the difference between the sum of these quantities
and the sum of their mathematical expectations. Namely, it is clear from Chebyshev's reasoning
that this law of large numbers must hold in all those cases when the mathematical expectation of
the square of the difference between the sum of the quantities and the sum of their
mathematical expectations, as the number of quantities increases without bound, grows more
slowly than the square of their number, so that the ratio of this mathematical expectation to
the square of the number of quantities has the limit zero.

In his derivations Chebyshev restricted himself to the simplest, and therefore the most
interesting, case of independent quantities; in this simplest case, as Che-

> \*) Works of P. L. Chebyshev, vol. I. On mean values.

**[p. 136]** byshev showed, the mathematical expectation of the above-mentioned square, as the
number of quantities increases without bound, can grow only as fast as their number, if the
mathematical expectations of the squares of the quantities themselves remain finite and do not
increase without bound.

Of course, Chebyshev's conditions are far from exhausting all the cases to which the above law
can be applied, even if we restrict ourselves to independent quantities. We do not, however,
intend to occupy ourselves with the search for conditions necessary and sufficient for the
applicability of this law; we shall only point out that Chebyshev's conclusions can be extended
also to some cases, of a fairly general character, when the quantities depend on each other.

**§ 1.** In the first place one can put the case when the connection between the quantities is
such that an increase of any one of them entails a decrease of the mathematical expectations of
the others.

Let us dwell on this case; let the quantities under consideration be

$$x_1, x_2, \ldots, x_n, \ldots,$$

and let their mathematical expectations be respectively

$$a_1, a_2, \ldots, a_n, \ldots;$$

let us further put for brevity

$$x_l - a_l = z_l.$$

Considering the mathematical expectation of the square

$$(z_1 + z_2 + \cdots + z_n)^2,$$

we decompose it into the terms

$$z_1^2 + z_2^2 + \cdots + z_n^2 + 2z_1z_2 + 2z_1z_3 + \cdots + 2z_{n-1}z_n$$

**[p. 137]** and use the well-known proposition that the mathematical expectation of a sum is
equal to the sum of the mathematical expectations of the terms.

For independent quantities the mathematical expectations of the products of the form $z_lz_k$
are all equal to zero, and therefore the mathematical expectation $(z_1 + z_2 + \cdots + z_n)^2$
reduces to the sum of the mathematical expectations of the squares of the quantities
$z_1, z_2, \ldots, z_n$. In our case, however, the mathematical expectation of each product
$z_lz_k$ is a negative number, and therefore

$$\text{math. expect. } (z_1 + z_2 + \cdots + z_n)^2 < \Sigma \text{ math. expect. } z_k^2 \quad (k = 1, 2, \ldots, n).$$

To convince ourselves of this, let us suppose that the set of numbers

$$z_l', z_l'', \ldots, z_l^{(\omega)},$$

arranged in increasing order, represents all the possible values of $z_l$, and that their
probabilities are respectively equal to

$$p_l', p_l'', \ldots, p_l^{(\omega)};$$

let, finally, when

$$z_l = z_l', z_l'', \ldots, z_l^{(\omega)}$$

the mathematical expectation of $z_k$ be respectively equal to

$$a_k', a_k'', \ldots, a_k^{(\omega)}.$$

With these notations the mathematical expectation of the product $z_lz_k$ is expressed by the sum

$$p_l'z_l'a_k' + p_l''z_l''a_k'' + \cdots + p_l^{(\omega)}z_l^{(\omega)}a_k^{(\omega)},$$

while the mathematical expectations of the quantities $z_l, z_k$ themselves, which are equal to
zero, can be represented in the form of the sums

$$p_l'z_l' + p_l''z_l'' + \cdots + p_l^{(\omega)}z_l^{(\omega)}$$

and

$$p_l'a_k' + p_l''a_k'' + \cdots + p_l^{(\omega)}a_k^{(\omega)}.$$

**[p. 138]** And since for the case under consideration we must have, by assumption,

$$a_k' > a_k'' > \cdots > a_k^{(\omega)},$$

then by virtue of a well-known inequality of Chebyshev\*) we have

$$\sum p_l^{(i)} z_l^{(i)} a_k^{(i)} < \sum p_l^{(i)} z_l^{(i)} \sum p_l^{(i)} a_k^{(i)} = 0.$$

[In the original the index $(i)$ is written above each letter.]

Consequently the law of large numbers can be applied to the case under consideration, provided
only that the mathematical expectation $z_n$ [*sic*; presumably $z_n^2$ is meant] remains finite
and does not increase without bound together with $n$.

To the same inequality

$$\text{math. expect. } (z_1 + z_2 + \cdots + z_n)^2 < \Sigma \text{ math. expect. } z_k^2,$$

and hence to the same conclusion about the applicability of the law of large numbers, it is not
difficult to come also in the case when the mathematical expectation of $x_k$, for every $k$,
decreases as the sum

$$x_1 + x_2 + \cdots + x_{k-1}$$

increases; for this one need only use the identity

$$(z_1 + z_2 + \cdots + z_n)^2 = z_1^2 + z_2^2 + \cdots + z_n^2 + 2z_1z_2 + 2(z_1 + z_2)z_3 + 2(z_1 + z_2 + z_3)z_4 + \cdots$$

The stated conditions are fulfilled, for example, in the case when the sum

$$x_1 + x_2 + \cdots + x_n$$

is equal to the number of white balls among $n$ balls drawn in succession from an urn under the
following conditions:

> \*) Works of P. L. Chebyshev, vol. II, pp. 716–719. On approximate expressions of some
> integrals in terms of others. Korkine. *Sur un théorème de M. Tchébycheff* (Comptes Rendus,
> t. XCVI).

**[p. 139]**

1. the initial number of white balls in the urn is $2a$, and of the other balls $2b$;
2. the balls drawn are not returned to the urn;
3. when $a + b$ balls remain in the urn, $a$ white balls and $b$ other balls are added to it.

By virtue of the law of large numbers we may in this case, exactly as in the well-known case
when the ratio of the number of white balls to the number of all balls in the urn keeps the
constant value $\frac{a}{a+b}$, assert with a probability as close to certainty as we wish that
the ratio of the number of white balls that have appeared to the number of all balls drawn will,
when their number is sufficiently large, differ from $\frac{a}{a+b}$ by less than any given
quantity.

**§ 2.** Repeating that we give only sufficient, not necessary, conditions, let us dwell on one
of those cases to which Chebyshev's conclusions can be extended for the reason that the
influence of the quantities

$$x_1, x_2, \ldots, x_n, \ldots$$

on each other decreases rapidly as their mutual distance increases. In our case

$$x_1 + x_2 + \cdots + x_n$$

will represent the number of occurrences of some event $A$ in $n$ successive trials, connected
in such a way that the probability of the event $A$ at each trial has a fully determined value
$p'$ if the event $A$ occurred at the immediately preceding trial, and another determined value
$p''$ in the opposite case,

**[p. 140]** whatever the results of the other preceding trials may be; and if the results of
all the trials remain undetermined, then the probability of the event $A$ for each of them is
equal to one and the same number $p$.

Proceeding to the consideration of this case, let us put for brevity

$$1 - p = q, \quad 1 - p' = q', \quad 1 - p'' = q''$$

and note that the numbers $p, p', p''$ are connected with each other by the simple equality

$$p = pp' + qp'',$$

on the basis of which it is not difficult to find the third of these numbers from the other two;
it gives

$$p = \frac{p''}{1 - p' + p''}, \quad p' = 1 + p'' - \frac{p''}{p}, \quad p'' = p\,\frac{1 - p'}{1 - p}.$$

Since the numbers $x_l, x_k$ denote respectively the number ($0$ or $1$) of occurrences of the
event $A$ at the trials marked by the numbers $l$ and $k$, it is not difficult to establish the
equalities

$$a_l = a_k = p.$$

It is also not difficult to verify that the mathematical expectation of the product $z_lz_k$,
which is equal to

$$x_lx_k - a_lx_k - a_kx_l + a_ka_l,$$

reduces to the difference

$$\text{math. expect. } x_lx_k - p^2.$$

[A reader has written "$z_l = x_l - a_l$" by hand in the margin of the scanned copy.]

As for the mathematical expectation of the product $x_lx_k$, it is equal to the probability of
the occurrence of the event $A$ at both trials marked by the numbers $l$ and $k$, which in its

**[p. 141]** turn, by the theorem on the multiplication of probabilities, can be expressed by the
product of the number $p$, which represents the probability of the occurrence of the event $A$ at
the trial with number $l$, by a certain number $R^l_k$, which represents the probability of the
occurrence of the event $A$ at the trial with number $k$ when it is known that the event $A$
occurred at the trial with number $l$.

Having thus arrived at the equality

$$\text{math. expect. } z_lz_k = p(R^l_k - p),$$

we must occupy ourselves with finding the number $R^l_k$, which depends, as it is not difficult
to verify, only on the difference $k - l$, and can therefore be denoted by the simpler symbol

$$R_{k-l}.$$

For $k - l = 1$ we have, by our conditions,

$$R_1 = p';$$

it is then not difficult to find successively

$$R_2 = R_1p' + (1 - R_1)p'' = p'p' + q'p'',$$
$$R_3 = R_2p' + (1 - R_2)p'',$$
$$\cdots\cdots\cdots$$
$$R_{m+1} = R_mp' + (1 - R_m)p'' = p'' + (p' - p'')R_m.$$

The equation

$$R_{m+1} = p'' + (p' - p'')R_m$$

belongs to the number of those for whose solution it is not difficult to indicate a general
formula; namely, this equation gives us

$$R_m = p + C(p' - p'')^m,$$

where the constant number $C$ is determined from the condition

$$R_1 = p'$$

and turns out to be equal to $1 - p = q$.

**[p. 142]** Thus

$$\text{math. expect. } z_lz_k = pq(p' - p'')^{k-l}$$

and consequently

$$\text{math. expect. } (z_1 + z_2 + \cdots + z_{k-1})z_k = pq[p' - p'' + (p' - p'')^2 + \cdots + (p' - p'')^{k-1}].$$

[In the scanned copy the last exponent is overwritten by a handwritten "1"; $k - 1$ is what the
sum requires.]

It follows from this that for $p' < p''$ the mathematical expectation of the product

$$(z_1 + z_2 + \cdots + z_{k-1})z_k$$

is a negative number, and therefore

$$\text{math. expect. } (z_1 + z_2 + \cdots + z_n)^2 < npq;$$

if, however, $p' > p''$, then the mathematical expectation of the product

$$(z_1 + z_2 + \cdots + z_{k-1})z_k$$

is less than

$$\frac{pq(p' - p'')}{1 - p' + p''}$$

and therefore

$$\text{math. expect. } (z_1 + z_2 + \cdots + z_n)^2 < npq\Big(1 + \frac{2(p' - p'')}{1 - p' + p''}\Big) < \frac{npq\,(1 + p' - p'')}{1 - p' + p''}.$$

We have thus arrived at inequalities which clearly show that the law of large numbers can be
applied to the given case.

By virtue of this law we may, with a probability as close to certainty as we wish, assert that
for a sufficiently large number of our trials the ratio of the number of occurrences of the
event $A$ to the number of trials will differ from $p$ by a quantity smaller than any given
number.

**§ 3.** The expression for the mathematical expectation of the product

**[p. 143]** $z_lz_k$ found in the preceding section can be derived from general formulas, with
which we shall now occupy ourselves and which can serve as a basis for further investigations.

Let us denote, under the assumptions of the preceding section, by the symbol $P_{m,k}$ the
probability that in the first $k$ trials the event $A$ will occur exactly $m$ times.

We may put

$$P_{m,k} = V_{m,k} + U_{m,k},$$

where $U_{m,k}$ and $V_{m,k}$ denote the same probability as $P_{m,k}$, but under the following
conditions:

1. $U_{m,k}$ — under the condition that at the last trial the event $A$ does not take place;
2. $V_{m,k}$ — under the condition that at the last trial the event $A$ takes place.

In connection with the quantities $P_{m,k}, V_{m,k}, U_{m,k}$ let us introduce three more
functions of an arbitrary number $\xi$:

$$\Phi_k = U_{0,k} + U_{1,k}\xi + U_{2,k}\xi^2 + \cdots + U_{k-1,k}\xi^{k-1},$$
$$\Psi_k = V_{1,k}\xi + V_{2,k}\xi^2 + \cdots + V_{k,k}\xi^k,$$
$$\Omega_k = P_{0,k} + P_{1,k}\xi + P_{2,k}\xi^2 + \cdots + P_{k,k}\xi^k = \Psi_k + \Phi_k.$$

We shall now show that the function $\Omega_k$ can be determined as the coefficient of $t^k$ in
the expansion, in ascending powers of an arbitrary number $t$, of a fairly simple expression.

For this purpose, using the theorems on the addition and multiplication of probabilities, we
establish two equalities

$$U_{m,k} = q'V_{m,k-1} + q''U_{m,k-1},$$
$$V_{m,k} = p'V_{m-1,k-1} + p''U_{m-1,k-1}.$$

Applying then these equalities to the functions $\Phi_k$ and $\Psi_k$, we obtain two equations

**[p. 144]**

$$\Phi_k = q'\Psi_{k-1} + q''\Phi_{k-1},$$
$$\Psi_k = p'\xi\Psi_{k-1} + p''\xi\Phi_{k-1},$$

from which, finally, by eliminating one of the two functions $\Phi$ or $\Psi$, we derive

$$\Phi_{k+1} - (p'\xi + q'')\Phi_k + (p' - p'')\xi\Phi_{k-1} = 0,$$
$$\Psi_{k+1} - (p'\xi + q'')\Psi_k + (p' - p'')\xi\Psi_{k-1} = 0.$$

And since

$$\Omega_k = \Phi_k + \Psi_k,$$

we must also have

$$\Omega_{k+1} - (p'\xi + q'')\Omega_k + (p' - p'')\xi\Omega_{k-1} = 0.$$

It follows from this that $\Omega_k$ can be determined as the coefficient of $t^k$ in the
expansion, in ascending powers of $t$, of a fraction of the form

$$\frac{A + Bt}{1 - (p'\xi + q'')t + (p' - p'')\xi t^2},$$

where $A$ and $B$ do not depend on $t$.

To determine $A$ and $B$ it remains to consider $\Omega_k$ for two values of $k$; for $k = 1$ and
$k = 2$ we easily find

$$\Omega_1 = q + p\xi,$$
$$\Omega_2 = qq'' + (qp'' + pq')\xi + pp'\xi^2,$$

from which we derive

$$\Omega_0 = 1.$$

Expanding our fraction in ascending powers of $t$ and restricting ourselves to the first two
terms, we find

$$A + (B + p'\xi + q'')t = \Omega_0 + \Omega_1t = 1 + (q + p\xi)t,$$

which gives us two equalities

$$A = 1,$$
$$B = (p - p')\xi + q - q'',$$

**[p. 145]** the latter of which is not difficult to bring to the form

$$B = (p'' - p')(q\xi + p).$$

Thus we finally find

$$\frac{1 + (p'' - p')(q\xi + p)t}{1 - (p'\xi + q'')t + (p' - p'')\xi t^2} = \Omega_0 + \Omega_1t + \Omega_2t^2 + \cdots.$$

This formula can serve as a basis for further investigations\*) and, in particular, from it one
can easily derive the results of the preceding section, on which, however, we shall not dwell.

> \*) See my article "Investigation of a remarkable case of dependent trials" in the Izvestiya
> of the Academy of Sciences for 1907.

**§ 4.** To clarify the matter let us give one more example, to which the law of large numbers
cannot be applied.

Let, as before (§ 1), the sum

$$x_1 + x_2 + \cdots + x_n$$

be equal to the number of white balls among $n$ balls drawn in succession from an urn, but under
new conditions, which we establish as follows:

1. the initial number of white balls in the urn is $a$, and of the others $b$;
2. each ball drawn from the urn goes back into the urn together with another ball of the same
   colour.

In the given case an increase of the sum

$$x_1 + x_2 + \cdots + x_{k-1}$$

necessarily leads to an increase of the mathematical expectation of $x_k$, and therefore the
mathematical expectation of the product

$$(z_1 + z_2 + \cdots + z_{k-1})z_k$$

turns out to be a positive number.

**[p. 146]** To compute the mathematical expectation of the square

$$(z_1 + z_2 + \cdots + z_n)^2$$

let us note that it can be expressed by the sum

$$\sum \Big(m - n\frac{a}{a+b}\Big)^2 P^{a,b}_{m,n} \quad (m = 0, 1, 2, \ldots, n),$$

where $P^{a,b}_{m,n}$ denotes the probability that among the $n$ balls drawn there will be
exactly $m$ white ones, and is determined, as it is not difficult to verify, by the formula

$$P^{a,b}_{m,n} = \frac{1.2.3\ldots n.\,a(a+1)\ldots(a+m-1)\,b(b+1)\ldots(b+n-m-1)}{1.2\ldots m.\,1.2\ldots(n-m)\,(a+b)(a+b+1)\ldots(a+b+n-1)}.$$

From this formula follow the following simple equalities

$$mP^{a,b}_{m,n} = \frac{na}{a+b}P^{a+1,b}_{m-1,n-1},$$
$$m(m-1)P^{a,b}_{m,n} = \frac{n(n-1)a(a+1)}{(a+b)(a+b+1)}P^{a+2,b}_{m-2,n-2},$$

on the basis of which we obtain

$$\sum mP^{a,b}_{m,n} = \frac{na}{a+b},$$
$$\sum m(m-1)P^{a,b}_{m,n} = \frac{n(n-1)a(a+1)}{(a+b)(a+b+1)},$$

where

$$m = 0, 1, 2, \ldots, n.$$

These last equalities, together with the obvious equality

$$\sum P^{a,b}_{m,n} = 1,$$

make it possible to determine the required sum

$$\sum \Big(m - n\frac{a}{a+b}\Big)^2 P^{a,b}_{m,n},$$

for which it should be decomposed into three parts:

**[p. 147]**

$$\sum m(m-1)P^{a,b}_{m,n} - \Big(\frac{2na}{a+b} - 1\Big)\sum mP^{a,b}_{m,n} + n^2\Big(\frac{a}{a+b}\Big)^2\sum P^{a,b}_{m,n}.$$

It remains to carry out simple calculations, on completing which we obtain

$$\sum \Big(m - n\frac{a}{a+b}\Big)^2 P^{a,b}_{m,n} = \frac{nab(n + a + b)}{(a+b)^2(a+b+1)}.$$

Relying on this result, we can show that the law of large numbers is not applicable to the given
case; so that for a sufficiently small value of $\varepsilon$ the probability of the inequalities

$$-\varepsilon \le \frac{m}{n} - \frac{a}{a+b} \le +\varepsilon$$

cannot be arbitrarily close to unity, however large the number $n$ may be.

For this purpose let us denote by the letter $\beta$ the probability of the non-fulfilment of the
inequalities

$$-\varepsilon \le \frac{m}{n} - \frac{a}{a+b} \le +\varepsilon$$

and take into account that the square

$$\Big(\frac{m}{n} - \frac{a}{a+b}\Big)^2$$

cannot exceed the larger of the numbers

$$\Big(\frac{a}{a+b}\Big)^2 \text{ and } \Big(\frac{b}{a+b}\Big)^2,$$

which we shall denote by the letter $\xi$.

With these notations it is not difficult to derive from the formula we have found the inequality

**[p. 148]**

$$\xi\beta > \frac{ab}{(a+b)^2(a+b+1)} - \varepsilon^2,$$

which shows that $\beta$ cannot be arbitrarily small, provided only that

$$\varepsilon < \sqrt{\frac{ab}{(a+b)^2(a+b+1)}}.$$

It is interesting to note that in our example the most probable value of the number $m$, which
we shall denote by the letter $\mu$, is determined by the simple inequalities

$$(a-1)n - b + 1 \le (a+b-2)\mu,$$
$$(a-1)n + a - 1 \le (a+b-2)\mu,$$

[In the scanned copy the sign in the second inequality is partly overwritten by hand and is hard
to read; for $\mu$ to be the most probable value the second inequality must be
$(a-1)n + a - 1 \ge (a+b-2)\mu$.]

and the ratio $\frac{\mu}{n}$, as $n$ increases without bound, has as its limit

$$\text{not } \frac{a}{a+b} \text{ but } \frac{a-1}{a+b-2};$$

but of course one cannot count on the ratio $\frac{m}{n}$ being, for large values of $n$,
arbitrarily close to $\frac{a-1}{a+b-2}$; since the mathematical expectation of the square
$\big(\frac{m}{n} - g\big)^2$ attains its smallest value at $g = \frac{a}{a+b}$, and this smallest
value, as is seen from the formula we have found, tends, as $n$ increases without bound, to the
limit $\frac{ab}{(a+b)^2(a+b+1)}$, which is different from zero.

In the simplest case, when

$$a = b = 1,$$

**[p. 149]** the inapplicability of the law of large numbers is obvious; since in this case all
the suppositions

$$m = 0, 1, 2, 3, \ldots, n$$

have one and the same probability $\frac{1}{n+1}$.

*16 January 1907.*

**§ 5.** The conclusions of § 2 can be given considerably greater generality; namely, instead of
the number of occurrences of some event one can consider a sum of quantities connected in a
chain in such a way that, when one of them receives a definite value, the ones following it
become independent of those preceding it. Let

$$x_1, x_2, \ldots, x_k, x_{k+1}, \ldots$$

be an infinite series of quantities connected in such a way that $x_{k+1}$, for every $k$, does
not depend on

$$x_1, x_2, \ldots, x_{k-1},$$

when the value of $x_k$ is known.

Let further the set of numbers

$$\alpha, \beta, \gamma, \ldots$$

represent all the possible values of any of our quantities, and let the system

$$p_{\alpha,\alpha},\ p_{\alpha,\beta},\ p_{\alpha,\gamma},\ \ldots$$
$$p_{\beta,\alpha},\ p_{\beta,\beta},\ p_{\beta,\gamma},\ \ldots$$
$$\cdots\cdots\cdots$$

represent the probabilities, for a given value of $x_k$, that the quantity $x_{k+1}$ has a
definite value, the first

**[p. 150]** index of $p$ indicating the given value of $x_k$, and the second the supposed value
of $x_{k+1}$; for example, when

$$x_k = \beta$$

the probability of the equality

$$x_{k+1} = \gamma$$

has the value $p_{\beta,\gamma}$.

We suppose these probabilities to be independent of the index $k$, so as not to complicate our
notations and reasoning too much.

Let, finally,

$$p^{(k)}_\alpha,\ p^{(k)}_\beta,\ p^{(k)}_\gamma,\ \ldots$$

denote respectively the probabilities for $x_k$ to have the values

$$\alpha, \beta, \gamma, \ldots$$

while all the quantities

$$x_1, x_2, x_3, \ldots$$

remain undetermined. The numbers

$$p_{\alpha,\alpha},\ p_{\alpha,\beta},\ p_{\alpha,\gamma},\ \ldots$$
$$p_{\beta,\alpha},\ p_{\beta,\beta},\ p_{\beta,\gamma},\ \ldots$$
$$\cdots\cdots\cdots$$

must of course be positive; besides, they must satisfy the equalities

$$p_{\alpha,\alpha} + p_{\alpha,\beta} + p_{\alpha,\gamma} + \cdots = 1,$$
$$p_{\beta,\alpha} + p_{\beta,\beta} + p_{\beta,\gamma} + \cdots = 1,$$
$$\cdots\cdots\cdots;$$

by no other conditions are these numbers restricted.

**[p. 151]** As for the numbers

$$p^{(k)}_\alpha,\ p^{(k)}_\beta,\ p^{(k)}_\gamma,\ \ldots,$$

which of course must satisfy the condition

$$p^{(k)}_\alpha + p^{(k)}_\beta + p^{(k)}_\gamma + \cdots = 1,$$

they cannot be assigned independently for all values of $k$: on the contrary, from the values

$$p'_\alpha,\ p'_\beta,\ p'_\gamma,\ \ldots$$

one can compute successively all the quantities

$$p^{(k)}_\alpha,\ p^{(k)}_\beta,\ p^{(k)}_\gamma,\ \ldots$$

on the basis of the simple formulas

$$p^{(k+1)}_\alpha = p_{\alpha,\alpha}p^{(k)}_\alpha + p_{\beta,\alpha}p^{(k)}_\beta + \cdots$$
$$p^{(k+1)}_\beta = p_{\alpha,\beta}p^{(k)}_\alpha + p_{\beta,\beta}p^{(k)}_\beta + \cdots$$
$$\cdots\cdots\cdots$$

Turning to the mathematical expectations of our quantities under various data, let us denote as
before by the symbol

$$a_k$$

the mathematical expectation of $x_k$ while all the quantities

$$x_1, x_2, \ldots, x_k, \ldots$$

remain undetermined, and by the symbols

$$A^{(i)}_\alpha,\ A^{(i)}_\beta,\ A^{(i)}_\gamma,\ \ldots$$

the mathematical expectations of the quantity

$$x_{k+i}$$

**[p. 152]** respectively when

$$x_k = \alpha,\ x_k = \beta,\ x_k = \gamma,\ \ldots.$$

With these notations it is not difficult to establish the following equalities

$$a_k = p^{(k)}_\alpha\alpha + p^{(k)}_\beta\beta + p^{(k)}_\gamma\gamma + \cdots$$
$$a_{k+i} = p^{(k)}_\alpha A^{(i)}_\alpha + p^{(k)}_\beta A^{(i)}_\beta + p^{(k)}_\gamma A^{(i)}_\gamma + \cdots$$
$$A^{(i)}_\alpha = p_{\alpha,\alpha}A^{(i-1)}_\alpha + p_{\alpha,\beta}A^{(i-1)}_\beta + p_{\alpha,\gamma}A^{(i-1)}_\gamma + \cdots$$
$$A^{(i)}_\beta = p_{\beta,\alpha}A^{(i-1)}_\alpha + p_{\beta,\beta}A^{(i-1)}_\beta + p_{\beta,\gamma}A^{(i-1)}_\gamma + \cdots$$
$$\cdots\cdots\cdots$$

On the basis of these equalities we shall prove that all the quantities

$$a_{k+i},\ A^{(i)}_\alpha,\ A^{(i)}_\beta,\ A^{(i)}_\gamma,\ \ldots,$$

as the number $i$ increases without bound, approach one limit. For this purpose let us first of
all note that, by virtue of the equalities we have given, the number $a_{k+i}$ lies between the
greatest and the least of the numbers

$$A^{(i)}_\alpha,\ A^{(i)}_\beta,\ A^{(i)}_\gamma,\ \ldots,$$

and these latter numbers all lie between the greatest and the least of the numbers

$$A^{(i-1)}_\alpha,\ A^{(i-1)}_\beta,\ A^{(i-1)}_\gamma,\ \ldots.$$

Considering then the difference

$$A^{(i)}_\alpha - A^{(i)}_\beta,$$

we obtain on the basis of the same formulas

**[p. 153]**

$$A^{(i)}_\alpha - A^{(i)}_\beta = (p_{\alpha,\alpha} - p_{\beta,\alpha})A^{(i-1)}_\alpha + (p_{\alpha,\beta} - p_{\beta,\beta})A^{(i-1)}_\beta + \cdots$$

and since the sum

$$(p_{\alpha,\alpha} - p_{\beta,\alpha}) + (p_{\alpha,\beta} - p_{\beta,\beta}) + \cdots$$

is equal to zero, then, separating in the system

$$p_{\alpha,\alpha} - p_{\beta,\alpha},\ p_{\alpha,\beta} - p_{\beta,\beta},\ \ldots$$

the positive numbers from the negative ones and replacing the latter by their numerical values,
we obtain two sets of positive numbers forming equal sums.

It is important to note also that these sums are less than unity; for the terms of one of them
are less than

$$p_{\alpha,\alpha},\ p_{\alpha,\beta},\ p_{\alpha,\gamma},\ \ldots$$

and the terms of the other are less than

$$p_{\beta,\alpha},\ p_{\beta,\beta},\ p_{\beta,\gamma},\ \ldots.$$

Therefore, replacing some of the numbers

$$A^{(i-1)}_\alpha,\ A^{(i-1)}_\beta,\ A^{(i-1)}_\gamma,\ \ldots$$

by the greatest, and others by the least of them, and denoting by the symbol

$$\Delta^{(i-1)}$$

the difference between the greatest and the least of our numbers

$$A^{(i-1)}_\alpha,\ A^{(i-1)}_\beta,\ A^{(i-1)}_\gamma,\ \ldots,$$

we can establish the inequality

$$\text{num. val. } \big(A^{(i)}_\alpha - A^{(i)}_\beta\big) < h\Delta^{(i-1)},$$

where $h$ is equal to the sum of all the positive numbers of the system

$$p_{\alpha,\alpha} - p_{\beta,\alpha},\ p_{\alpha,\beta} - p_{\beta,\beta},\ \ldots$$

**[p. 154]** and is less than unity.

An entirely similar conclusion can be drawn regarding the difference of any two numbers of the
system

$$A^{(i)}_\alpha,\ A^{(i)}_\beta,\ A^{(i)}_\gamma,\ \ldots.$$

Therefore, considering instead of

$$A^{(i)}_\alpha - A^{(i)}_\beta$$

the difference $\Delta^{(i)}$ between the greatest and the least of the numbers

$$A^{(i)}_\alpha,\ A^{(i)}_\beta,\ A^{(i)}_\gamma,\ \ldots,$$

we can establish the inequality

$$\Delta^{(i)} < H\Delta^{(i-1)},$$

where $H$ denotes some constant number lying between $0$ and $1$.

This inequality shows that $\Delta^{(i)}$ approaches the limit zero when $i$ increases without
bound.

Consequently, as the number $i$ increases without bound, all the quantities

$$a_{k+i},\ A^{(i)}_\alpha,\ A^{(i)}_\beta,\ A^{(i)}_\gamma,\ \ldots$$

approach one limit, from which they differ by a quantity less than $\Delta^{(i)}$; at the same
time we have

$$\Delta^{(i)} < CH^i,$$

where $C$ and $H$ are constant numbers and

$$0 < H < 1.$$

Turning then to the mathematical expectation of the square

$$(x_1 - a_1 + x_2 - a_2 + \cdots + x_n - a_n)^2,$$

we decompose this square into the same terms as

**[p. 155]** in § 2, putting

$$x_k - a_k = z_k.$$

And by virtue of what has been proved, reasoning exactly as in § 2, we easily arrive at the
inequalities

$$\text{math. expect. } z_k(z_1 + z_2 + \cdots + z_{k-1}) < D(H + H^2 + \cdots + H^{k-1})$$

and

$$\text{math. expect. } (x_1 - a_1 + x_2 - a_2 + \cdots + x_n - a_n)^2 < Gn,$$

where $D$ and $G$ are constant numbers.

On the other hand, comparing the mathematical expectation

$$(x_1 - a_1 + x_2 - a_2 + \cdots + x_n - a_n)^2$$

with the mathematical expectation

$$(x_1 + x_2 + \cdots + x_n - na)^2,$$

where

$$a = \text{lim. } a_{k+i} \quad (i = \infty),$$

we find that the difference of the mathematical expectations of these squares is equal to

$$(a_1 - a + a_2 - a + \cdots + a_n - a)^2$$

and keeps a finite value as the number $n$ increases without bound. Consequently, as the number
$n$ increases without bound, the mathematical expectation of the square

$$\Big(\frac{x_1 + x_2 + \cdots + x_n}{n} - a\Big)^2$$

must approach the limit zero.

And from this there follows at once, for the given case, the law of large numbers: however small
the positive numbers $\varepsilon$ and $\eta$ may be, the probability of the fulfilment of the
inequalities

$$-\varepsilon < \frac{x_1 + x_2 + \cdots + x_n}{n} - a < \varepsilon$$

**[p. 156]** will be greater than $1 - \eta$ for all sufficiently large values of $n$.

Thus the independence of the quantities is not a necessary condition for the existence of the
law of large numbers.

*25 March 1907.*

**A. Markov.**
