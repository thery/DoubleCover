# Computing Hard-to-Round Inputs of the binary64 Exponential Function

*Paul Zimmermann*

We split the search by considering all binary64 inputs $x$ such that
$\exp(x)$ lies in the binade $[2^{e-1}, 2^e)$. For the binade
$[2^{1023}, 2^{1024})$, this gives $x_0 \le x \le x_1$, with
$x_0 = \texttt{0x1.628b76e3a7b61p+9}$ and $x_1 = \texttt{0x1.62e42fefa39efp+9}$.
We have about $2^{42.5}$ binary64 numbers to check in $[x_0, x_1]$. We further
split the range $[x_0, x_1]$ into subranges, so that each subrange has at most
$2^{32.7}$ values. In our example, splitting in 874 subranges is enough.

Let $u = \mathrm{ulp}(x)$ for $x \in [x_0, x_1]$. (If $x_0$ and $x_1$ are not
in the same binade, we split the range, this happens for example for the
output binade $[2^{738}, 2^{739})$.) In our example, we have $u = 2^{-43}$. We
use the Taylor expansion of $\exp(x)$ around $x = x_0$ with explicit
remainder:

$$\exp(x_0 + ju) = a_0 + a_1 j + a_2 j^2 + \cdots + a_{k-1} j^{k-1} + r,$$

with $a_i = \exp(x_0) u^i / i!$, and $|r| \le \exp(x_1) (nu)^k / k!$, with
$x_1 = x_0 + nu$. Let $v = \frac{1}{2} \mathrm{ulp}(\exp(x))$ for
$x_0 \le x \le x_1$. In our example, we have $v = 2^{970}$. It follows:

$$\frac{\exp(x_0 + ju)}{v} = \frac{a_0}{v} + \frac{a_1}{v} j + \cdots
  + \frac{a_{k-1} j^{k-1}}{v} + \frac{r}{v}.$$

In our example, with $k = 8$, the error term $\frac{r}{v}$ is less than
$2^{-43.7}$ in absolute value.

If $x = x_0 + ju$ is a hard-to-round input, then $\exp(x)$ is very close to
$v$, thus the fractional part of $\exp(x)/v$ is very small. More precisely, if
$\exp(x)$ has 43 identical bits or more after the round bit, then
$|\mathrm{frac}(\exp(x)/v)| < 2^{-43}$, with a centered fractional part in
$[-1/2, 1/2)$.

The polynomial
$\mathrm{frac}(a_0/v) + \mathrm{frac}(a_1/v) j + \cdots
  + \mathrm{frac}(a_{k-1}/v) j^{k-1}$
is approximated using the table-of-differences method, with each term
$\mathrm{frac}(a_i/v)$ approximated by $A_i \beta^{-\ell}$, where $A_i$ is an
integer, satisfying $0 \le A_i < \beta^\ell$ and
$|A_i - \beta^\ell \mathrm{frac}(a_i/v)| < 1$, where $\beta = 2^{64}$ is the
machine word basis. The error coming from the approximations $A_i$ is bounded
by:

$$(1 + n + \cdots + n^{k-1}) \beta^{-\ell}.$$

In our example, with $n \le 2^{32.7}$, $k = 8$ and $\ell = 5$, this yields an
error less than $2^{-91}$. Let $E$ be an integer such that
$E \ge \beta^\ell (2^{-43} + 2^{-43.7} + 2^{-91})$, then it suffices to check
values such that:

$$(A_0 + j A_1 + j^2 A_2 + \cdots + j^{k-1} A_{k-1}) \bmod \beta^\ell \le E,$$

where the remainder $\bmod\ \beta^\ell$ is taken centered. A classical trick is
to compute $A'_0 = A_0 + E \bmod \beta^\ell$, and check instead:

$$(A'_0 + j A_1 + j^2 A_2 + \cdots + j^{k-1} A_{k-1}) \bmod \beta^\ell \le 2E,$$

where the remainder is now taken non-negative.

The coefficients $A_i$ can be computed by any arbitrary-precision tool, for
example with SageMath. Then all further computations are with integers only,
thus are exact. For example, on a Intel Core Ultra 7 265 with gcc 16.2.0,
checking a range of about $2^{32.7}$ values around $x = 709$ takes less than 5
minutes on one core. Thus a full search for $x \ge 1$ would take less than 60
core-years.

In summary, the algorithm is the following:

1. split the range of values to check into subranges $[x_0, x_1]$ containing
   each at most $2^{32.7}$ values, such that both $u = \mathrm{ulp}(x)$ and
   $v = \frac{1}{2} \mathrm{ulp}(\exp(x))$ are constant on each subrange;
2. on each subrange $[x_0, x_1]$ such that $x_1 - x_0 = nu$, use an
   arbitrary-precision software to generate approximations of
   $a_i = \exp(x_0) u^i / i!$ for $0 \le i < k$, and deduce $\ell$-word
   integers $A_i$ such that
   $$|A_i - \beta^\ell \mathrm{frac}(a_i/v)| < 1;$$
3. from the $A_i$, compute $\ell$-word integers $B_i$, $0 \le i < k$ such
   that:
   $$B_i = A_0 + i A_1 + i^2 A_2 + \cdots + i^{k-1} A_{k-1} \bmod \beta^\ell;$$
4. perform the following loop to initialize the table-of-differences method:
   for $i = 1, \ldots, k-1$ do for $j = k-1, \ldots, i$ do
   $B_j \leftarrow B_j - B_{j-1} \bmod \beta^\ell$;
5. $B_0 \leftarrow B_0 + E \bmod \beta^\ell$;
6. (main loop) for $j = 0, \ldots, n$ do:
   - if $B_0 \le 2E$, then check if $x_0 + ju$ is a hard-to-round case.
   - for $i = 0, \ldots, k-2$ do $B_i \leftarrow B_i + B_{i+1} \bmod \beta^\ell$.
