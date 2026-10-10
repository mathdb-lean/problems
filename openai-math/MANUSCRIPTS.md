# OpenAI math manuscripts

Every manuscript in [openai/math](https://github.com/openai/math) at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, whether or not it has a
Lean statement. The ones that do are obligations in this benchmark under the
`openai-math` collection; the rest are what remains to be formalized.

| | |
|---|---|
| manuscripts | 719 |
| result families | 372 |
| with a comparator challenge (formalized main result) | 338 |
| without a Lean statement | 381 |
| withdrawn by `history.md` | 0 |

Nothing here is mirrored: titles, abstracts and links only. `manuscripts.json`
carries the same rows for a program.

## 001. Milne’s rationality conjecture and algebraic specialization

Proves Milne's rationality conjecture for abelian varieties over $`\overline{\mathbb Q}`$ with good reduction: specialized Hodge classes pair rationally with complementary divisor products, independently of cohomology theory. Together with result 032, every specialized Hodge class is represented by a single rational algebraic cycle simultaneously in all prime-to-p and crystalline realizations, for every residue characteristic p.

- [Milne's rationality conjecture for abelian varieties](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Milnes-rationality-conjecture-for-abelian-varieties-October-7-2026/paper.pdf) -- no Lean statement
## 002. The full BSD formula from low Selmer corank

Proves the full Birch–Swinnerton-Dyer leading-term formula for every elliptic curve over ℚ whose full q-power Selmer group has corank zero or one for some prime q, including finiteness of the Tate–Shafarevich group. With result 006, this gives full BSD for a density-one set of quadratic twists of every elliptic curve over ℚ.

- [Exact Birch–Swinnerton-Dyer Formula from Low Selmer Corank](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Birch-Swinnerton-Dyer-Formula-from-Low-Selmer-Corank-October-7-2026/exact-bsd-low-selmer-corank.pdf) -- no Lean statement
- [The Selmer converse for elliptic curves at every prime](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Selmer-converse-for-elliptic-curves-at-every-prime-October-7-2026/main.pdf) -- no Lean statement
- [The two-primary Birch–Swinnerton-Dyer formula in Selmer corank at most one](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-two-primary-Birch-Swinnerton-Dyer-formula-in-Selmer-corank-at-most-one-October-6-2026/paper.pdf) -- no Lean statement
## 003. The quasi-Riemann hypothesis

Proves that every Dirichlet L-function, including $`\zeta(s)`$, is zero-free in $`\Re s\gt 7/8`$, resolving the quasi-Riemann hypothesis. The same half-plane is zero-free for every finite-order Hecke L-function over $`\mathbb Q(\sqrt{-3})`$. A companion gives a different proof of the zero-free half-plane $`\Re s\gt 11/12`$. ([Lean](lean/docs/003.md))

- [The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $`\Re s\gt 7/8`$ ](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) -- formalized: `QuasiRiemannHypothesis`, `DirichletSevenEighths`, `HeckeSevenEighths`, `SiegelZeros`
- [The Quasi-Riemann Hypothesis (alternate 11/12 proof)](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf) -- no Lean statement
- [Uniform exclusion of Landau–Siegel zeros](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026/paper.pdf) -- formalized: `QuasiRiemannHypothesis`, `DirichletSevenEighths`, `HeckeSevenEighths`, `SiegelZeros`
## 004. Hilbert’s tenth problem over ℚ

Proves that no algorithm decides whether an integer-coefficient polynomial in an arbitrary number of variables has a rational zero, resolving Hilbert's tenth problem over ℚ negatively.

- [Hilbert’s tenth problem over the rational numbers](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026/main.pdf) -- no Lean statement
- [A pointwise 2-converse for elliptic curves with rational two-torsion](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-pointwise-2-converse-for-elliptic-curves-with-rational-two-torsion-October-7-2026/paper.pdf) -- no Lean statement
## 005. Irrationality of Catalan’s constant

Proves that Catalan's constant $`G=\sum_{j\ge0}(-1)^j/(2j+1)^2`$ is irrational. ([Lean](lean/docs/005.md))

- [Catalan's constant is irrational](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf) -- formalized: `Catalan`
## 006. Goldfeld’s conjecture: densities and mean analytic rank

Proves Goldfeld's conjecture for quadratic twists of every elliptic curve over ℚ: analytic ranks zero and one each have density 1/2, and the mean analytic rank tends to 1/2. Both statements order signed squarefree twist parameters by absolute value.

- [Goldfeld's analytic density conjecture and the 2-converse for elliptic curves](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Goldfelds-analytic-density-conjecture-and-the-2-converse-for-elliptic-curves-October-7-2026/paper.pdf) -- no Lean statement
- [The mean analytic rank of quadratic twists of elliptic curves](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-mean-analytic-rank-of-quadratic-twists-of-elliptic-curves-October-6-2026/paper.pdf) -- no Lean statement
## 007. Ordinary two-point correlations and the corrected Elliott conjecture

Proves the ordinary two-point Chowla conjecture, with a bound $`O(X/(\log X)^c)`$ for Liouville correlation sums along fixed nonproportional affine forms, where c &gt; 0 is absolute. More generally, proves the binary corrected Elliott conjecture for complex multiplicative functions bounded by one when one factor is uniformly nonpretentious against each fixed Dirichlet character times $`n^{it}`$ for $`|t|\le X`$. ([Lean](lean/docs/007.md))

- [Ordinary two-point correlations of multiplicative functions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) -- formalized: `OrdinaryElliott`, `OrdinaryTwoPointCorrelations`
## 008. The Deligne–Drinfeld conjecture

Proves that the rational Grothendieck–Teichmüller Lie algebra, with the Ihara bracket, is freely generated by one element in each odd weight 3, 5, 7, …, resolving the Deligne–Drinfeld conjecture. ([Lean](lean/docs/008.md))

- [The Deligne-Drinfeld conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf) -- formalized: `DeligneDrinfeld`
## 009. Function-field reconstruction from Milnor K-theory and Galois data

Reconstructs function fields of transcendence degree at least two over algebraically closed constants from $`K^{\mathrm M}_1/\ell`$, $`K^{\mathrm M}_2/\ell`$, and their product. These data recover the perfect closure and constants when ℓ differs from the characteristic, and the original field and its named base in equal characteristic. Also proves Bogomolov–Pop reconstruction from abelian-by-central pro-ℓ Galois data away from the characteristic. ([Lean](lean/docs/009.md))

- [Reconstruction of Function Fields from Mod-ℓ Milnor K-Theory](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Reconstruction-of-Function-Fields-from-Mod-ell-Milnor-K-Theory-October-5-2026/mod-ell-bogomolov-pop.pdf) -- no Lean statement
- [Reconstruction from Milnor K-theory modulo the characteristic](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Reconstruction-from-Milnor-K-theory-modulo-the-characteristic-October-5-2026/paper.pdf) -- no Lean statement
- [The Bogomolov-Pop reconstruction theorem](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Bogomolov-Pop-reconstruction-theorem-September-23-2026/paper.pdf) -- formalized: `BogomolovPopInjectivity`
## 010. Unrestricted pro-modularity at the prime two

Every continuous odd absolutely irreducible two-dimensional 2-adic representation of $`G_{\mathbb Q}`$ unramified outside finitely many primes occurs in a completed Hecke algebra at some odd tame level. Also proves classical modularity up to Tate twist for irreducible odd representations with these finiteness conditions that are de Rham at 2 with distinct Hodge–Tate weights, resolving the dyadic Fontaine–Mazur case without residual restrictions.

- [Unrestricted pro-modularity at the prime two](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Unrestricted-pro-modularity-at-the-prime-two-October-6-2026/two-adic-promodularity.pdf) -- no Lean statement
- [The Dimension of the Two-Adic Hecke Algebra at Odd Level](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Dimension-of-the-Two-Adic-Hecke-Algebra-at-Odd-Level-October-5-2026/two-adic-hecke.pdf) -- no Lean statement
- [Fontaine–Mazur modularity at the prime 2](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Fontaine-Mazur-modularity-at-the-prime-2-October-6-2026/paper.pdf) -- no Lean statement
## 011. Prime-factor statistics of $`p-1`$

Proves that the normalized ordered logarithms of the prime factors of $`p-1`$, counted with multiplicity, converge jointly to the Poisson–Dirichlet law $`\mathrm{PD}(1)`$ as p ranges uniformly over primes up to x and $`x\to\infty`$. This resolves the Ford–Konyagin–Luca conjecture. It also proves that infinitely many integers n have more than $`n^{1-\varepsilon}`$ totient preimages, for every ε &gt; 0.

- [Weighted dilation graphs, smooth shifted primes and totient fibers](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/paper.pdf) -- no Lean statement
- [The Poisson-Dirichlet law for prime predecessors](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf) -- no Lean statement
- [Prime Predecessors with an Even Number of Prime Factors](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/paper.pdf) -- no Lean statement
## 012. Independent largest prime factors of consecutive integers

Resolves the Erdős–Pomerance joint Dickman conjecture: the logarithmic sizes of the largest prime factors of n and $`n+1`$ are asymptotically independent in ordinary natural density. In particular, the integers satisfying $`P^+(n)\lt P^+(n+1)`$ have density 1/2. ([Lean](lean/docs/012.md))

- [The joint Dickman law for consecutive integers](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf) -- formalized: `JointDickman`
## 013. Ostmann’s inverse Goldbach conjecture

Proves that no finite modification of the primes can be written as $`A+B`$ with $`A,B\subseteq\mathbb Z_{\ge0}`$ each containing at least two elements. This resolves Ostmann's inverse Goldbach conjecture on additive indecomposability. ([Lean](lean/docs/013.md))

- [The additive indecomposability of the primes](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf) -- formalized: `OstmannComplete`, `OstmannPrimes`
## 014. Restricted geometric Langlands, global Arthur enhancements, and generic Ramanujan

Proves the restricted geometric Langlands equivalence for connected reductive groups on smooth projective connected curves over $`\overline{\mathbb F}_q`$ under the four stated Lie-theoretic characteristic hypotheses. Over arbitrary algebraically closed fields of characteristic p &gt; 0, the same conclusion holds assuming additionally that p is very good for the group and $`p\nmid |W_G|`$. Over global function fields, proves Ramanujan at every place for globally generic cuspidal representations of split adjoint absolutely simple exceptional groups, without characteristic or ramification-depth restrictions, and at every unramified place for cuspidal representations of split adjoint absolutely simple groups with a generic unramified component. Assuming the finite-level Ramanujan–Arthur decomposition, constructs global Arthur enhancements of occurring cuspidal excursion parameters for split connected semisimple groups at full finite level, recovering the given parameters by diagonal specialization on the entire Weil group, including inertia.

- [Global Arthur Enhancements of Cuspidal Excursion Parameters](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Global-Arthur-Enhancements-of-Cuspidal-Excursion-Parameters-October-5-2026/manuscript.pdf) -- no Lean statement
- [Rationality of the Canonical Unramified Arthur Filtration](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Rationality-of-the-Canonical-Unramified-Arthur-Filtration-September-24-2026/paper.pdf) -- no Lean statement
- [Ramanujan-Arthur Decompositions of Cuspidal Functions at Full Finite Level](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ramanujan-Arthur-Decompositions-of-Cuspidal-Functions-at-Full-Finite-Level-September-24-2026/paper.pdf) -- no Lean statement
- [Temperedness at ramified places for globally generic exceptional groups](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Temperedness-at-ramified-places-for-globally-generic-exceptional-groups-October-5-2026/ramified-ramanujan.pdf) -- no Lean statement
- [The Restricted Geometric Langlands Equivalence in Positive Characteristic](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Restricted-Geometric-Langlands-Equivalence-in-Positive-Characteristic-September-24-2026/paper.pdf) -- no Lean statement
- [Constructible tame Hecke eigensheaves in positive characteristic](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Constructible-tame-Hecke-eigensheaves-in-positive-characteristic-October-5-2026/constructible-tame-hecke-eigensheaves-positive-characteristic.pdf) -- no Lean statement
- [Tame Hecke Eigensheaves with Several Marked Points](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Tame-Hecke-Eigensheaves-with-Several-Marked-Points-October-5-2026/Tame-Hecke-Eigensheaves-with-Several-Marked-Points.pdf) -- no Lean statement
- [Frobenius Structures on Tame Hecke Eigensheaves](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Frobenius-Structures-on-Tame-Hecke-Eigensheaves-October-5-2026/tame-hecke-frobenius.pdf) -- no Lean statement
## 015. Torus-packet equidistribution in prime, quartic, and sextic degrees

Proves Haar equidistribution without escape of mass for complete volume-weighted torus packets from totally real fields: arbitrary lattices and prescribed local types in fixed prime degree at least five, arbitrary-order Picard packets in primitive quartic fields, and maximal-order ideal-class packets in primitive sextic fields. Here primitive means having no proper intermediate field; the relevant order or field discriminant tends to infinity. ([Lean](lean/docs/015.md))

- [Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf) -- formalized: `DukePrimeDegree`
- [Equidistribution of primitive quartic torus packets for arbitrary orders](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equidistribution-of-Primitive-Quartic-Torus-Packets-for-Arbitrary-Orders-October-5-2026/quartic-torus-packets.pdf) -- no Lean statement
- [Equidistribution of Primitive Sextic Torus Packets](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equidistribution-of-Primitive-Sextic-Torus-Packets-October-5-2026/primitive-sextic-torus-packets.pdf) -- no Lean statement
## 016. Zilber–Pink in abelian varieties and the Siegel threefold

Proves the abelian Zilber–Pink conjecture over $`\overline{\mathbb Q}`$: every irreducible subvariety has finitely many maximal atypical subvarieties relative to its smallest containing torsion coset. It also proves the full curve case in the Siegel threefold $`\mathcal A_2`$ for Hodge-generic curves defined over $`\overline{\mathbb Q}`$, without boundary or reduction assumptions.

- [The abelian Zilber–Pink conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Abelian-Zilber-Pink-Conjecture-September-24-2026/paper.pdf) -- no Lean statement
- [The E×CM component of Zilber–Pink for curves in A2](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-E-times-CM-Component-of-Zilber-Pink-for-Curves-in-A2-September-24-2026/paper.pdf) -- no Lean statement
- [Quaternionic division points on curves in the Siegel threefold](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quaternionic-Division-Points-on-Curves-in-the-Siegel-Threefold-September-24-2026/paper.pdf) -- no Lean statement
- [Elliptic squares and Zilber–Pink for curves in A2](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Elliptic-Squares-and-Zilber-Pink-for-Curves-in-A2-September-24-2026/paper.pdf) -- no Lean statement
## 017. The irrationality exponent of <i>π</i> is 2

Proves that the irrationality exponent of π is exactly 2: for every ε &gt; 0 and all sufficiently large denominators q, every rational $`p/q`$ satisfies $`|\pi-p/q|\ge q^{-2-\varepsilon}`$. This also proves convergence of the Flint–Hills series $`\sum_{n\ge1}1/(n^3\sin^2 n)`$, with angles in radians. ([Lean](lean/docs/017.md))

- [The irrationality exponent of pi is 2](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf) -- formalized: `PiExponent`
## 018. The Margulis–Platonov conjecture over global fields

Proves the Margulis–Platonov conjecture over every global field, including function fields of characteristic two. For an absolutely almost simple simply connected algebraic group G over k, every noncentral abstract normal subgroup of $`G(k)`$ is the inverse image of an open normal subgroup in the finite product of its anisotropic nonarchimedean local groups.

- [The Margulis–Platonov conjecture over global function fields](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Margulis-Platonov-conjecture-over-global-function-fields-October-5-2026/margulis-platonov-global-function-fields.pdf) -- no Lean statement
- [The Margulis–Platonov conjecture over number fields](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Margulis-Platonov-conjecture-over-number-fields-September-23-2026/paper.pdf) -- no Lean statement
## 019. The local <i>p</i>-adic section conjecture and global consequences

Proves that rational points on every smooth proper geometrically connected curve of genus at least two over a finite extension of ℚp correspond bijectively to conjugacy classes of sections of its full arithmetic étale fundamental group. It also proves Grothendieck's section conjecture over ℚ for the modular curves $`X_0(N)`$ and $`X_1(N)`$ of genus at least two.

- [Étale covers with a prescribed exterior sheet](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Etale-covers-with-a-prescribed-exterior-sheet-September-24-2026/main.pdf) -- no Lean statement
- [The p-adic section conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-p-adic-section-conjecture-October-6-2026/main.pdf) -- no Lean statement
## 020. Squarefree quartics and power-free polynomial values

Proves the squarefree-values conjecture for irreducible integer quartics with no fixed prime-square divisor: squarefree values on positive integers have the predicted positive Euler-product density. More generally, establishes the $`(d-2)`$-power-free density for irreducible integer polynomials of degrees four through eight under the necessary local condition; together with Browning's higher-degree theorem, this covers every d ≥ 4. ([Lean](lean/docs/020.md))

- [Squarefree values of quartics and power-free values of polynomials](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026/manuscript.pdf) -- formalized: `PowerFreeValues`
## 021. A quadratic bound for Jacobsthal’s function

Answers Jacobsthal's quadratic-bound question: every interval of $`Ck^2`$ consecutive integers contains an integer coprime to any prescribed positive integer with at most k distinct prime divisors, for an absolute constant C. The bound is uniform over prime sets and interval positions and removes the classical logarithmic loss. ([Lean](lean/docs/021.md))

- [A quadratic bound for Jacobsthal's function](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf) -- formalized: `Jacobsthal`, `JacobsthalImproved`
## 022. The weak inhomogeneous Duffin–Schaeffer conjecture

Proves that for every real shift γ and finite-valued $`\psi:\mathbb N\to[0,\infty)`$, divergence of $`\sum_q\phi(q)\psi(q)/q`$ implies $`\|qx-\gamma\|\lt \psi(q)`$ for infinitely many q, for almost every x. Here ϕ is Euler's totient and the norm is distance to the nearest integer. Numerators are unrestricted; no monotonicity or Diophantine condition on γ is needed.

- [The Weak Inhomogeneous Duffin–Schaeffer Conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-weak-inhomogeneous-Duffin-Schaeffer-conjecture-September-25-2026/paper.pdf) -- no Lean statement
## 023. Patterson's first moment for cubic Gauss sums

Proves unconditionally the all-primary-prime form of Patterson’s first-moment asymptotic: normalized cubic Gauss sums over primary Eisenstein primes of norm at most X, including both conjugates, have an explicit positive main term of order $`X^{5/6}/\log X`$. Every fixed nonzero prime-angle Fourier mode has smaller order. ([Lean](lean/docs/023.md))

- [An unconditional first moment for cubic Gauss sums](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf) -- formalized: `PattersonFirstMoment`
## 024. An asymptotic formula for the number of totients

Gives an asymptotic equivalent for the number $`V(x)`$ of distinct totient values up to x, with a positive bounded phase-dependent factor determined by convergent arithmetic approximations. In particular, $`V(cx)/V(x)\to c`$ for every fixed c &gt; 0, answering Erdős and Hall’s scaling question. ([Lean](lean/docs/024.md))

- [An asymptotic formula for the number of totients](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-asymptotic-formula-for-the-number-of-totients-September-25-2026/An-asymptotic-formula-for-the-number-of-totients-September-25-2026.pdf) -- formalized: `TotientAsymptotic`, `TotientCompanionZero`
## 025. Short Egyptian fractions

Every rational $`a/b`$ with $`1\le a\lt b`$ is a sum of $`O(\log\log b)`$ distinct positive unit fractions. The worst-case minimum number of terms has the same order, resolving Erdős’s conjecture on short Egyptian fractions. ([Lean](lean/docs/025.md))

- [Short Egyptian fractions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Short-Egyptian-fractions-September-25-2026/Short-Egyptian-fractions-September-25-2026.pdf) -- formalized: `EgyptianFractions`, `ShortEgyptianFractions`
## 026. Positive lower density of large prime gaps

For every fixed C &gt; 0, a positive proportion of consecutive prime gaps exceed $`C\log p_n`$, throughout every sufficiently large initial segment of the primes. The proportion may depend on C. Consequently, the indices where $`p_n/n`$ increases have positive lower density, answering Erdős and Prachar. ([Lean](lean/docs/026.md))

- [Positive lower density of large prime gaps](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Positive-lower-density-of-large-prime-gaps-September-25-2026/main.pdf) -- formalized: `PrimeGaps`
## 027. Potential integral density on curve character varieties

Resolves the determinant-one curve case of Litt's integral-density question. For every smooth connected complex algebraic curve and every rank, integral points become Zariski dense in every component of its SLr character variety over the full ring of integers of one number field. Prescribed quasi-unipotent boundary conjugacy classes are allowed, including nonsemisimple classes. ([Lean](lean/docs/027.md))

- [Integral points on character varieties of curves](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Integral-points-on-character-varieties-of-curves-September-25-2026/paper.pdf) -- formalized: `CharacterVarietiesAllSeamsSupport`
## 028. Uniformly bounded components of Gaussian-prime graphs

Proves the Gaussian moat conjecture: no infinite walk through distinct Gaussian primes can have uniformly bounded steps. More strongly, for every distance bound D, the graph joining Gaussian primes at distance at most D has uniformly bounded finite component sizes, depending only on D, including primes on the coordinate axes. ([Lean](lean/docs/028.md))

- [Bounded-Step Walks on Gaussian Primes](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Bounded-Step-Walks-on-Gaussian-Primes-September-26-2026/paper.pdf) -- formalized: `GaussianMoat`
## 029. Primitive roots for every admissible integer base

Proves the infinitude assertion in Artin's primitive root conjecture for every integer a that is neither −1 nor a square. For each such base, at least $`c_a x/(\log x)^2`$ primes in every sufficiently large interval $`(x,2x)`$ have primitive root a, with $`c_a\gt 0`$.

- [Primitive roots for every admissible integer base](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf) -- no Lean statement
- [Simultaneous primitive roots: a conditional lower bound for prime bases](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Simultaneous-primitive-roots-a-conditional-lower-bound-for-prime-bases-October-4-2026/simultaneous-primitive-roots-conditional-lower-bound-prime-bases.pdf) -- no Lean statement
## 030. Modularity of elliptic curves over imaginary quadratic fields

Proves the modularity conjecture for elliptic curves over imaginary quadratic fields: every elliptic curve over every imaginary quadratic field is modular, with matching local parameters at every place.

- [Modularity of elliptic curves over imaginary quadratic fields](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Modularity-of-elliptic-curves-over-imaginary-quadratic-fields-October-4-2026/paper.pdf) -- no Lean statement
## 031. Uchida’s conjecture for open homomorphisms of Galois groups

Proves Uchida's conjecture: every continuous open homomorphism between Galois groups of possibly infinite solvably closed Galois extensions of number fields comes from a unique equivariant field embedding in the opposite direction. No restriction on the kernel or separate cyclotomic-compatibility assumption is needed.

- [Open Homomorphisms of Global Solvably Closed Galois Groups](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Open-Homomorphisms-of-Global-Solvably-Closed-Galois-Groups-October-5-2026/open-homomorphisms-solvably-closed-galois-groups.pdf) -- no Lean statement
## 032. The rational Hodge conjecture for CM abelian varieties

Proves the rational Hodge conjecture for every complex CM abelian variety, in every dimension and codimension. Through Milne's theorems, this also gives the Tate conjecture for all abelian varieties over finite fields and the Hodge standard conjecture for abelian varieties in every characteristic.

- [The rational Hodge conjecture for CM abelian varieties](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-rational-Hodge-conjecture-for-CM-abelian-varieties-October-6-2026/paper.pdf) -- no Lean statement
- [Algebraic Kuga–Satake correspondences and Hodge conjectures on a K3 quadratic locus](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Algebraic-Kuga-Satake-correspondences-and-Hodge-conjectures-on-a-K3-quadratic-locus-September-30-2026/paper.pdf) -- no Lean statement
- [Weil classes and Hodge classes on abelian powers](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Weil-classes-and-Hodge-classes-on-abelian-powers-October-6-2026/paper.pdf) -- no Lean statement
- [Abelian covers, Gale correspondences, and the Hodge conjecture for powers](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Abelian-covers-Gale-correspondences-and-the-Hodge-conjecture-for-powers-October-6-2026/paper.pdf) -- no Lean statement
- [A Conditional Reduction for Algebraic Kuga–Satake Correspondences](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Conditional-Reduction-for-Algebraic-Kuga-Satake-Correspondences-September-10-2026/paper.pdf) -- no Lean statement
## 033. Iitaka subadditivity, variation, and logarithmic additivity

Proves Campana's orbifold Iitaka subadditivity conjecture for smooth Fujiki-class-$`\mathcal C`$ manifolds with rational simple-normal-crossing boundaries. For projective fibrations $`f:U\to V`$ of smooth complex quasi-projective varieties with connected fibers, general fiber F, and $`\bar\kappa(V)\ge0`$, proves Popa's inequality $`\bar\kappa(U)\ge\kappa(F)+\max\{\bar\kappa(V),\mathop{\mathrm{Var}}\nolimits (f)\}`$, where variation measures the whole geometric generic fiber. ([Lean](lean/docs/033.md))

- [Orbifold and logarithmic Iitaka subadditivity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Orbifold-and-logarithmic-Iitaka-subadditivity-September-26-2026/paper.pdf) -- no Lean statement
- [Logarithmic Kodaira dimension and whole-fiber variation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Logarithmic-Kodaira-dimension-and-whole-fiber-variation-September-26-2026/paper.pdf) -- no Lean statement
- [The reverse logarithmic Kodaira inequality and additivity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-reverse-logarithmic-Kodaira-inequality-and-additivity-September-26-2026/paper.pdf) -- formalized: `LogKodairaFiberNegative`
- [Projective Hodge lines and ordinary Iitaka subadditivity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Projective-Hodge-lines-and-ordinary-Iitaka-subadditivity-September-27-2026/paper.pdf) -- no Lean statement
- [B-semiampleness for compact log-smooth Kähler fibrations](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/B-semiampleness-for-compact-log-smooth-Kahler-fibrations-September-10-2026/paper.pdf) -- no Lean statement
## 034. Log abundance for compact Kähler spaces under logarithmic Iitaka subadditivity

Using logarithmic Iitaka subadditivity, proves log abundance in every dimension for normal compact Kähler log canonical pairs with effective rational boundary: an analytically nef ℚ-Cartier adjoint is semiample. It also proves projective log abundance over every algebraically closed field of characteristic zero and the effective Iitaka fibration conjecture for smooth projective varieties of nonnegative Kodaira dimension in that setting. A further result resolves the finite-rational-coefficient index conjecture for connected projective semi-log-canonical log Calabi–Yau pairs over such fields in each fixed dimension and for each fixed finite set of rational boundary coefficients, with a uniform index independent of the number of components.

- [Log abundance for compact Kähler spaces under logarithmic Iitaka subadditivity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Log-abundance-for-compact-Kahler-spaces-under-logarithmic-Iitaka-subadditivity-October-6-2026/main.pdf) -- no Lean statement
- [Uniform indices for semi-log-canonical log Calabi–Yau pairs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-indices-for-semi-log-canonical-log-Calabi-Yau-pairs-October-5-2026/uniform-slc-index.pdf) -- no Lean statement
- [Conditional good minimal models for compact Kähler fourfolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Conditional-good-minimal-models-for-compact-Kahler-fourfolds-October-6-2026/paper.pdf) -- no Lean statement
- [Log abundance in characteristic zero](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Log-abundance-in-characteristic-zero-September-24-2026/paper.pdf) -- no Lean statement
- [Minimal metrics and interior injectivity for nef adjoints](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Minimal-metrics-and-interior-injectivity-for-nef-adjoints-September-27-2026/paper.pdf) -- no Lean statement
- [Fourfold nonvanishing by minimal metrics and moving jets](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Fourfold-nonvanishing-by-minimal-metrics-and-moving-jets-September-27-2026/paper.pdf) -- no Lean statement
- [Lifting sections from the reduced support of an adjoint](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Lifting-sections-from-the-reduced-support-of-an-adjoint-September-27-2026/paper.pdf) -- no Lean statement
- [Schnell fiber spaces and good canonical models](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Schnell-fiber-spaces-and-good-canonical-models-September-24-2026/paper.pdf) -- no Lean statement
- [Uniform log Iitaka fibrations and bounded moduli denominators](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-log-Iitaka-fibrations-and-bounded-moduli-denominators-October-4-2026/uniform-log-iitaka.pdf) -- no Lean statement
- [Uniform Pluricanonical Iitaka Fibrations](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Pluricanonical-Iitaka-Fibrations-October-3-2026/paper.pdf) -- no Lean statement
- [Relative denominators and effective systems for log Calabi-Yau fibrations](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Relative-denominators-and-effective-systems-for-log-Calabi-Yau-fibrations-September-27-2026/paper.pdf) -- no Lean statement
- [Arithmetic Stein-degree bounds for log Calabi–Yau pairs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Arithmetic-Stein-degree-bounds-for-log-Calabi-Yau-pairs-September-25-2026/paper.pdf) -- no Lean statement
- [Uniform effective log Iitaka fibrations for fourfolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-effective-log-Iitaka-fibrations-for-fourfolds-September-26-2026/paper.pdf) -- no Lean statement
- [Abundance after nonvanishing for compact Kähler fourfolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Abundance-after-nonvanishing-for-compact-Kahler-fourfolds-September-27-2026/paper.pdf) -- no Lean statement
## 035. Log-canonical threefold abundance in numerical dimension one

Proves log abundance for projective log canonical threefold pairs over algebraically closed fields of characteristic p &gt; 3 when the effective boundary is rational and the ℚ-Cartier adjoint is nef of numerical dimension one. The adjoint is semiample, without requiring the original variety to be terminal or ℚ-factorial.

- [Log abundance in numerical dimension one for threefolds in positive characteristic](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Log-abundance-in-numerical-dimension-one-for-threefolds-in-positive-characteristic-October-5-2026/paper.pdf) -- no Lean statement
- [Abundance in numerical dimension one for terminal threefolds in positive characteristic](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Abundance-in-numerical-dimension-one-for-terminal-threefolds-in-positive-characteristic-September-24-2026/paper.pdf) -- no Lean statement
## 036. Numerical semiampleness and generalized minimal models

Proves numerical semiampleness for nef adjoints $`K_X+B+M`$ with $`K_X+B`$ pseudo-effective and M nef rational, for projective klt rational pairs over algebraically closed characteristic-zero fields and smooth compact Kähler rational klt simple-normal-crossing pairs, using Bott–Chern cohomology in the latter case. Separately, projective generalized log canonical rational pairs over such fields admit minimal models for pseudo-effective adjoints and Mori fiber spaces otherwise, with nef b-data fixed.

- [Numerical semiampleness of nef adjoint classes on compact Kähler manifolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Numerical-semiampleness-of-nef-adjoint-classes-on-compact-Kahler-manifolds-October-6-2026/numerical-generalized-abundance.pdf) -- no Lean statement
- [Numerical Semiampleness of Nef Adjoint Divisors](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Numerical-Semiampleness-of-Nef-Adjoint-Divisors-October-3-2026/paper.pdf) -- no Lean statement
- [Minimal models and Mori fibre spaces for generalized log canonical Q-pairs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Minimal-models-and-Mori-fibre-spaces-for-generalized-log-canonical-Q-pairs-September-24-2026/paper.pdf) -- no Lean statement
- [Minimal models in numerical dimension one](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Minimal-models-in-numerical-dimension-one-September-24-2026/paper.pdf) -- no Lean statement
## 037. The ordinary-double-point volume gap

Proves the ordinary-double-point volume-gap conjecture: every singular complex algebraic klt germ of dimension n ≥ 2, with zero boundary, has normalized volume at most $`2(n-1)^n`$. Equality holds precisely for an analytic ordinary double point.

- [The ordinary-double-point gap in every dimension](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-ordinary-double-point-gap-in-every-dimension-September-24-2026/paper.pdf) -- no Lean statement
- [The normalized-volume gap in dimension four](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-normalized-volume-gap-in-dimension-four-September-24-2026/paper.pdf) -- no Lean statement
## 038. Fujita’s freeness conjecture

Proves Fujita's freeness conjecture at its sharp bound in every dimension: for a smooth projective complex variety X of dimension n and an ample line bundle L, the adjoint $`K_X+mL`$ is globally generated for every integer $`m\ge n+1`$.

- [Fujita's freeness conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Fujitas-freeness-conjecture-September-23-2026/Fujitas-freeness-conjecture-September-23-2026.pdf) -- no Lean statement
## 039. Nagata’s conjecture and maximal Seshadri constants

Proves Nagata's strict inequality $`\sum_i m_i\lt d\sqrt r`$ for every nonzero effective plane curve of degree d through r ≥ 10 very general complex points, with arbitrary multiplicities mi. It also proves maximal multipoint Seshadri constants $`(L^n/r)^{1/n}`$ for every smooth polarized projective variety of dimension n ≥ 2 and all sufficiently large r: at very general points over ℂ, and at the geometric generic tuple over any algebraically closed field of positive characteristic. ([Lean](lean/docs/039.md))

- [Nagata's conjecture for plane curves](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Nagatas-Conjecture-for-Plane-Curves-September-23-2026/main.pdf) -- formalized: `Nagata`, `MaximalSeshadriConstants`
- [Maximal Seshadri constants on arbitrary polarized surfaces](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf) -- formalized: `Nagata`, `MaximalSeshadriConstants`
- [Maximal Multipoint Seshadri Constants in Higher Dimensions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Maximal-Multipoint-Seshadri-Constants-in-Higher-Dimensions-October-5-2026/main.pdf) -- no Lean statement
- [Maximal multipoint Seshadri constants in positive characteristic](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Maximal-multipoint-Seshadri-constants-in-positive-characteristic-October-5-2026/seshadri-positive-characteristic.pdf) -- no Lean statement
## 040. Bloch’s conjecture for complex surfaces

Proves Bloch's conjecture: for every smooth connected projective complex surface S with $`p_g(S)=0`$, the Albanese map $`\mathrm{CH}_0(S)^0\to\mathrm{Alb}(S)(\mathbb C)`$ on integral degree-zero zero-cycles is an isomorphism. This combines the new $`p_g=q=0`$ theorem with the classical theorem of Bloch, Kas, and Lieberman.

- [Bloch’s conjecture for surfaces with p_g=0](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Blochs-Conjecture-for-Surfaces-with-pg-equals-q-equals-0-September-24-2026/paper.pdf) -- no Lean statement
## 041. Hyperkähler SYZ and projective-space bases

Proves the strong hyperkähler SYZ conjecture: every holomorphic line bundle with nonzero nef isotropic first Chern class on a compact irreducible holomorphic symplectic Kähler manifold is semiample. It also proves that every projective Lagrangian fibration with normal projective base has projective space as its base, in every dimension and deformation type.

- [Projective-space bases of Lagrangian fibrations](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Projective-Space-Bases-of-Lagrangian-Fibrations-September-23-2026/main.pdf) -- no Lean statement
- [The strong hyperkähler SYZ conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Strong-Hyperkahler-SYZ-Conjecture-September-23-2026/main.pdf) -- no Lean statement
## 042. Oka classification for minimal compact complex surfaces: Kodaira dimension zero and class VII

Proves that every complex K3 surface is Oka, including nonprojective surfaces. More generally, every connected minimal compact complex surface of Kodaira dimension zero is Oka; a connected minimal compact complex surface of class VII is Oka exactly when it is a Hopf or Enoki surface.

- [Every complex K3 surface is Oka](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Every-complex-K3-surface-is-Oka-September-23-2026/paper.pdf) -- no Lean statement
## 043. <i>P</i> = <i>W</i> for fixed-determinant SL<sub><i>n</i></sub> moduli spaces

Proves $`P_k=W_{2k}=W_{2k+1}`$ on the full rational cohomology of smooth coprime fixed-determinant, trace-free Higgs moduli spaces and their character varieties for composite ranks over smooth projective complex curves of genus at least two. This includes variant cohomology and, together with the known prime-rank theorems, establishes the fixed-determinant P = W conjecture in every coprime rank.

- [P=W in composite rank for fixed determinant](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/P-equals-W-in-composite-rank-for-fixed-determinant-September-24-2026/P-equals-W-in-composite-rank-for-fixed-determinant-September-24-2026.pdf) -- no Lean statement
## 044. The equivariant cohomological Hikita conjecture

Proves the equivariant cohomological Hikita correspondence for every finite quiver, including loops and multiple arrows, with arbitrary dimension and framing vectors and commuting flavor torus. When every semistable point is stable and the gauge action is free, the equivariant cohomology of the Nakajima variety is canonically the coordinate ring of the scheme-theoretic cocharacter-fixed locus of its flavor-deformed Coulomb branch.

- [The equivariant cohomological Hikita conjecture for arbitrary quivers](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-equivariant-cohomological-Hikita-conjecture-for-arbitrary-quivers-September-24-2026/main.pdf) -- no Lean statement
## 046. Shafarevich counterexamples in dimension two and with large fundamental group

Constructs a smooth projective complex fourfold with large fundamental group whose universal cover contains no positive-dimensional compact analytic subvariety but is neither Stein nor holomorphically convex. A separate smooth projective complex surface already disproves unrestricted Shafarevich holomorphic convexity in dimension two.

- [A projective fourfold with large fundamental group and non-Stein universal cover](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-projective-fourfold-with-large-fundamental-group-and-non-Stein-universal-cover-October-5-2026/large-fundamental-group-non-stein.pdf) -- no Lean statement
- [A surface counterexample to Shafarevich holomorphic convexity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-surface-counterexample-to-Shafarevich-holomorphic-convexity-September-23-2026/paper.pdf) -- no Lean statement
## 047. Zariski cancellation and affine fibrations over the complex numbers

Constructs an integral complex affine fourfold $`X\not\cong\mathbb A^4`$ with $`X\times\mathbb A^1\cong\mathbb A^5`$, disproving affine-space cancellation over ℂ in dimension four. It also disproves the Dolgachev–Weisfeiler affine-fibration conjecture: smooth surjections $`X\to\mathbb A^1`$ and $`\mathbb A^5\to\mathbb A^2`$ have every residue-field fiber isomorphic to affine three-space but are not Zariski-locally trivial. ([Lean](lean/docs/047.md))

- [An explicit failure of complex affine-space cancellation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-failure-of-complex-affine-space-cancellation-September-23-2026/paper.pdf) -- formalized: `ComplexCancellation`
## 048. A characteristic-zero counterexample to Lipman–Zariski

Constructs a singular normal affine complex surface with free rank-two tangent sheaf, disproving the characteristic-zero Lipman–Zariski conjecture.

- [A singular normal affine surface with free tangent sheaf](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-singular-normal-affine-surface-with-free-tangent-sheaf-September-23-2026/paper.pdf) -- no Lean statement
## 049. A stable-coordinate counterexample in four variables

Constructs a polynomial in four complex variables that is not a coordinate but becomes one after adjoining a single variable, disproving the Stable Coordinate conjecture in four variables. Every fiber is affine three-space, yet none of its embeddings is rectifiable, also disproving the Abhyankar–Sathaye conjecture even when all fibers are affine spaces. ([Lean](lean/docs/049.md))

- [A stable coordinate that is not a coordinate in four variables](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-stable-coordinate-that-is-not-a-coordinate-in-four-variables-October-5-2026/stable-coordinate-four-variables.pdf) -- formalized: `AbhyankarSathaye`, `CommutingDerivations`, `StableCoordinateFour`
- [An explicit noncoordinate polynomial with affine three-space zero fibre](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-noncoordinate-polynomial-with-affine-three-space-zero-fibre-September-24-2026/paper.pdf) -- formalized: `AbhyankarSathaye`, `CommutingDerivations`, `StableCoordinateFour`
## 050. A counterexample to Griffiths’ positivity conjecture

Constructs ample rank-two bundles on $`\mathbb P^1\times\mathbb P^1`$ with no smooth Hermitian metric of strictly Griffiths-positive curvature, disproving Griffiths' positivity conjecture already on the quadric surface. ([Lean](lean/docs/050.md))

- [Ample rank-two bundles on the quadric surface without Griffiths-positive metrics](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/ample-rank-two-bundles-on-the-quadric-surface-without-griffiths-positive-metrics-September-24-2026/paper.pdf) -- formalized: `QuadricBundles`
## 051. Kobayashi’s canonical-ampleness conjecture

Every compact connected Kähler manifold of positive complex dimension with no nonconstant entire curve has ample canonical bundle and is therefore projective. This proves Kobayashi's canonical-ampleness conjecture in the smooth compact Kähler setting.

- [Canonical ampleness of compact hyperbolic Kähler manifolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Canonical-ampleness-of-compact-hyperbolic-Kahler-manifolds-September-23-2026/canonical-ampleness.pdf) -- no Lean statement
## 052. Tangent splittings and product decompositions

A splitting of the tangent bundle of a compact Kähler manifold into two integrable holomorphic subbundles induces a compatible product decomposition of its universal cover, proving the two-summand form of Beauville's splitting conjecture. On smooth rationally connected projective manifolds, both summands are automatically integrable, establishing Höring's conjecture and the corresponding product decomposition. ([Lean](lean/docs/052.md))

- [Universal-cover splitting for compact Kähler manifolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Universal-cover-splitting-for-compact-Kahler-manifolds-September-23-2026/paper.pdf) -- formalized: `KahlerSplitting`, `SplitTangentIntegrability`
- [Integrability of split tangent bundles on rationally connected manifolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Integrability-of-split-tangent-bundles-on-rationally-connected-manifolds-September-23-2026/main.pdf) -- formalized: `KahlerSplitting`, `SplitTangentIntegrability`
## 053. A counterexample to Pixton completeness in Chow

Constructs a tautological relation on a moduli space of stable pointed curves that vanishes in rational Chow, hence in rational cohomology, but lies outside Pixton's original relation span. This disproves the Chow and rational-cohomological forms of his original completeness conjecture.

- [A high-arity counterexample to Pixton completeness in Chow](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-high-arity-counterexample-to-Pixton-completeness-in-Chow-September-24-2026/paper.pdf) -- no Lean statement
## 054. Irrational cubic fourfolds with Hodge-theoretic and categorical K3 associations

For every sufficiently large admissible Hassett discriminant, a very general smooth complex cubic fourfold is irrational despite having both an untwisted geometric K3 category and an integral Hodge-theoretic K3 association. This disproves Kuznetsov's rationality conjecture and the sufficiency of the associated-K3 criterion for rationality; the discriminant threshold is ineffective.

- [Irrational cubic fourfolds with geometric K3 categories](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Irrational-cubic-fourfolds-with-geometric-K3-categories-September-24-2026/Irrational-cubic-fourfolds-with-geometric-K3-categories-September-24-2026.pdf) -- no Lean statement
## 055. Gepner symmetry and large-volume stability on threefolds

Proves Toda's Gepner conjecture for every smooth complex quintic threefold, constructing a numerical Bridgeland stability condition with the prescribed phase shift 2/5. Also constructs numerical Bridgeland stability conditions at every sufficiently large volume on all smooth projective complex threefolds with trivial canonical bundle, with the exact ordinary and square-root-Todd central charges.

- [A Gepner stability condition on every smooth quintic threefold](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Gepner-stability-condition-on-every-smooth-quintic-threefold-September-24-2026/paper.pdf) -- no Lean statement
- [Prescribed large-volume charges on threefolds with trivial canonical bundle](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Prescribed-large-volume-charges-on-threefolds-with-trivial-canonical-bundle-September-24-2026/paper.pdf) -- no Lean statement
## 056. Termination of projective and Kähler fourfold minimal model programs

Proves termination of every existing generalized log canonical flip sequence on globally Weil ℚ-factorial compact Kähler fourfolds, with rational boundary, fixed rational analytically nef b-data, and projective small flip diagrams with the prescribed ample signs. Also proves termination of arbitrary permitted minimal model programs for projective log canonical fourfolds with rational boundary in characteristic zero.

- [Termination of generalized log canonical flips on compact Kähler fourfolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Termination-of-generalized-log-canonical-flips-on-compact-Kahler-fourfolds-October-7-2026/termination-generalized-lc-kahler-fourfolds.pdf) -- no Lean statement
- [Termination of generalized-canonical flips on compact Kähler fourfolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Termination-of-generalized-canonical-flips-on-compact-Kahler-fourfolds-October-6-2026/termination-generalized-terminal-flips-compact-kahler-fourfolds.pdf) -- no Lean statement
- [Termination for projective log canonical fourfolds with rational boundary](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Termination-for-projective-log-canonical-fourfolds-with-rational-boundary-September-24-2026/paper.pdf) -- no Lean statement
- [Finite ordinary minimal model programs on compact Kähler fourfolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-ordinary-minimal-model-programs-on-compact-Kahler-fourfolds-October-6-2026/paper.pdf) -- no Lean statement
- [Finite ordinary minimal model programs on compact Kähler fourfolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-ordinary-minimal-model-programs-on-compact-Kahler-fourfolds-September-24-2026/paper.pdf) -- no Lean statement
## 057. Fundamental groups of special complex varieties and root orbifolds

Proves Campana's abelianity conjecture: special compact Kähler manifolds have virtually abelian fundamental groups. Using this theorem, establishes the same conclusion for order-two root orbifolds of smooth projective complex fourfolds along one nonempty smooth connected divisor, when special in the stated differential-line sense. For smooth special complex quasi-projective varieties, proves that every finite-dimensional complex linear representation of the fundamental group has virtually nilpotent image of class at most two.

- [The abelianity conjecture for special compact Kähler manifolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-abelianity-conjecture-for-special-compact-Kahler-manifolds-September-23-2026/paper.pdf) -- no Lean statement
- [Two-step monodromy of special quasi-projective varieties](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Two-step-monodromy-of-special-quasi-projective-varieties-September-24-2026/paper.pdf) -- no Lean statement
- [A conditional abelianity theorem for special fourfold pairs with a half-weight divisor](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-conditional-abelianity-theorem-for-special-fourfold-pairs-with-a-half-weight-divisor-October-5-2026/main.pdf) -- no Lean statement
## 058. Semialgebraic universal covers and bounded domains

Proves the Kollár–Pardon conjecture: the semialgebraic universal covers of connected normal projective complex varieties are exactly products $`D\times\mathbb C^m\times F`$, with D bounded symmetric and F simply connected, normal, and projective. A universal cover is quasi-projective exactly when the bounded symmetric factor is absent. In particular, a smooth projective variety covered by ℂn has a finite étale cover by an abelian variety. ([Lean](lean/docs/058.md))

- [Semialgebraic universal covers of normal projective varieties](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Semialgebraic-universal-covers-of-normal-projective-varieties-September-24-2026/paper.pdf) -- no Lean statement
- [Symmetry of semialgebraic bounded domains with compact quotient](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf) -- formalized: `SymmetricDomains`
## 059. Counterexamples to Zariski’s multiplicity conjecture

Disproves Zariski's multiplicity conjecture by constructing reduced holomorphic hypersurface germs that are ambiently homeomorphic but have different multiplicities. The examples include hypersurfaces in ℂ4 with isolated critical points and multiplicities four and five.

- [Ambiently homeomorphic isolated hypersurfaces of multiplicities two and three](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ambiently-homeomorphic-isolated-hypersurfaces-of-multiplicities-two-and-three-September-24-2026/paper.pdf) -- no Lean statement
- [Ambiently homeomorphic isolated hypersurface germs in ℂ⁴ with multiplicities four and five](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ambiently-homeomorphic-isolated-hypersurface-germs-in-C4-with-multiplicities-four-and-five-September-27-2026/paper.pdf) -- no Lean statement
## 060. The Global Spherical Shell conjecture

Every connected minimal compact complex surface of class VII with $`b_2\gt 0`$ contains a global spherical shell, proving the positive-b2 Global Spherical Shell conjecture. Such a shell is a holomorphically embedded neighborhood of the standard three-sphere in $`\mathbb C^2\setminus\{0\}`$ whose complement is connected.

- [Global Spherical Shells on Minimal Surfaces of Class VII](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Global-Spherical-Shells-on-Minimal-Surfaces-of-Class-VII-September-24-2026/paper.pdf) -- no Lean statement
## 062. Projective contact classification and the LeBrun–Salamon conjecture

Proves the LeBrun–Salamon conjecture: every closed connected positive quaternionic-Kähler manifold of real dimension at least eight is homothetic to a compact symmetric Wolf space. It also proves contact-Fano homogeneity and classifies smooth connected complex projective contact manifolds of complex dimension at least three: those with $`b_2=1`$ are adjoint varieties with their canonical contact structures, while those with $`b_2\ge2`$ have underlying manifold $`\mathbb P(T^*Z)`$ for a smooth projective variety Z.

- [Contact Fano manifolds and the LeBrun–Salamon conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Contact-Fano-manifolds-and-the-LeBrun-Salamon-conjecture-September-23-2026/paper.pdf) -- no Lean statement
## 063. The generalized Mukai conjecture

Proves the generalized Mukai conjecture: every positive-dimensional smooth complex projective Fano manifold of dimension n, Picard number ρ and pseudoindex ι satisfies $`\rho(\iota-1)\le n`$, with equality exactly for $`(\mathbb P^{\iota-1})^\rho`$. Here the pseudoindex is the least anticanonical degree of a rational curve.

- [The generalized Mukai conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Generalized-Mukai-Conjecture-September-24-2026/article.pdf) -- no Lean statement
## 064. Topological triviality of <i>μ</i>-constant surface singularities

Proves topological right-triviality for every holomorphic one-parameter family of isolated hypersurface singularities in ℂ3 with constant Milnor number, resolving the surface case of the μ-constant problem. After shrinking the parameter disk and representatives, ambient homeomorphisms vary jointly continuously, fix the origin section and preserve the defining functions.

- [Topological triviality of mu-constant families of surface singularities](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Topological-triviality-of-mu-constant-families-of-surface-singularities-September-24-2026/main.pdf) -- no Lean statement
## 065. Virasoro constraints for complete intersections and projective-bundle towers

Proves the full ordinary unreduced descendant Virasoro conjecture for smooth complete intersections in complex projective space, in every genus and curve class with arbitrary cohomology insertions. The constraints also pass from any smooth projective complex base satisfying them to the projectivization of every algebraic vector bundle of rank at least two, and hence to projective-bundle towers.

- [Virasoro Constraints under Projectivization](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Virasoro-Constraints-under-Projectivization-October-5-2026/virasoro-constraints-under-projectivization.pdf) -- no Lean statement
- [Virasoro Constraints for Projective Complete Intersections](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Virasoro-Constraints-for-Projective-Complete-Intersections-September-24-2026/article.pdf) -- no Lean statement
## 066. Bounded klt complements for Fano contractions

Proves the finite-rational-coefficient form of Shokurov’s bounded-klt-complement conjecture for ϵ-lc complex Fano-type pairs with nef anti-log-canonical divisor. For ϵ-lc Fano contractions over any algebraically closed characteristic-zero field, it gives klt complements near every base point, with index bounded only by dimension and positive rational ϵ. ([Lean](lean/docs/066.md))

- [Bounded klt complements for Fano contractions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Bounded-klt-complements-for-Fano-contractions-September-25-2026/Bounded-klt-complements-for-Fano-contractions-September-25-2026.pdf) -- no Lean statement
- [Uniform Cartier sections for Fano type contractions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Cartier-sections-for-Fano-type-contractions-September-25-2026/Uniform-Cartier-sections-for-Fano-type-contractions-September-25-2026.pdf) -- formalized: `CartierChartCompactnessSupport`
## 067. The Campana–Peternell conjecture in dimension six

Proves the Campana–Peternell conjecture in complex dimension six: every smooth connected complex projective Fano sixfold with nef tangent bundle is rational homogeneous.

- [The Campana–Peternell conjecture in dimension six](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Campana-Peternell-conjecture-in-dimension-six-September-25-2026/main.pdf) -- no Lean statement
## 068. Anticanonical nonvanishing in every dimension

If X is a smooth connected complex projective variety and $`-K_X`$ admits a smooth Hermitian metric with nonnegative curvature, then $`H^0(X,-mK_X)\ne0`$ for some m &gt; 0. Thus smooth semipositivity forces a nonzero section of a positive tensor power of the anticanonical bundle in every dimension.

- [Anticanonical nonvanishing from smooth semipositivity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Anticanonical-nonvanishing-from-smooth-semipositivity-September-26-2026/main.pdf) -- no Lean statement
- [Invariant anticanonical indices and conversion of twisted differentials](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Invariant-anticanonical-indices-and-conversion-of-twisted-differentials-September-26-2026/main.pdf) -- no Lean statement
- [Bounded anticanonical metrics on klt pairs and torus quotients](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Bounded-anticanonical-metrics-on-klt-pairs-and-torus-quotients-September-26-2026/main.pdf) -- no Lean statement
- [Cohomological transfer and equivariant anticanonical sections](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Cohomological-transfer-and-equivariant-anticanonical-sections-September-26-2026/main.pdf) -- no Lean statement
- [Metric descent and rank-preserving contractions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Metric-descent-and-rank-preserving-contractions-September-26-2026/main.pdf) -- no Lean statement
- [Integrable metrics and effectivity with controlled boundary](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Integrable-metrics-and-effectivity-with-controlled-boundary-September-26-2026/main.pdf) -- no Lean statement
- [Exact orders and invariant anticanonical linear systems](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-orders-and-invariant-anticanonical-linear-systems-September-26-2026/main.pdf) -- no Lean statement
## 069. Global quantum geometric Langlands at irrational level

Proves the unramified de Rham quantum geometric Langlands equivalence for every connected simple complex algebraic group on every smooth projective connected complex curve, at every shifted level $`c\in\mathbb C\setminus\mathbb Q`$. It identifies the full derived categories of twisted D-modules for the group and its Langlands dual, retaining all global forms and connected components.

- [Global quantum geometric Langlands at irrational level](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Global-quantum-geometric-Langlands-at-irrational-level-October-4-2026/quantum-langlands.pdf) -- no Lean statement
## 071. Koebe’s circle-domain conjecture

Resolves the existence part of Koebe's circle-domain conjecture: every domain in the Riemann sphere is conformally equivalent to a domain whose complementary components are round disks or points. It also proves that circle domains with conformally removable boundary are rigid, meaning every conformal equivalence to another circle domain is Möbius, establishing this direction of the He–Schramm conjecture. ([Lean](lean/docs/071.md))

- [Removable Boundaries and Rigidity of Circle Domains](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Removable-Boundaries-and-Rigidity-of-Circle-Domains-September-23-2026/paper.pdf) -- formalized: `KoebeCircleDomains`
- [Koebe's Circle-Domain Conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf) -- formalized: `KoebeCircleDomains`
## 072. Brennan's conjecture and the integral-means spectrum

Proves Brennan's conjecture: for every conformal bijection ϕ from a simply connected plane domain onto the disk, $`|\phi'|^s`$ is area-integrable for $`4/3\lt s\lt 4`$. The sharp universal integral-means identity is $`B_{\mathcal S}(t)=|t|-1`$ for t ≤ −2. A strict bound $`B_b(-1)\lt 1/4`$ for bounded univalent functions disproves Kraetzer's prediction at that parameter. ([Lean](lean/docs/072.md))

- [Brennan's conjecture and sharp inverse-square integral means](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Brennans-conjecture-and-sharp-inverse-square-integral-means-September-24-2026/paper.pdf) -- formalized: `Brennan`, `BrennanSharp`, `StrictMeans`
- [A strict inverse-first-power bound for univalent functions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-strict-inverse-first-power-bound-for-univalent-functions-September-24-2026/paper.pdf) -- formalized: `Brennan`, `BrennanSharp`, `StrictMeans`
## 073. The Falconer distance conjecture

Resolves the Falconer distance conjecture in every dimension d ≥ 2: every compact set $`E\subset\mathbb R^d`$ with Hausdorff dimension greater than $`d/2`$ determines a set of Euclidean distances of positive Lebesgue measure. ([Lean](lean/docs/073.md))

- [The Falconer distance conjecture in all dimensions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf) -- formalized: `PlanarFalconer`, `FalconerAllDimensions`
## 074. Kakeya in three and four dimensions

Resolves the Kakeya maximal conjecture in three dimensions and the Hausdorff-dimension conjecture in four. In three dimensions, the radius-δ tube maximal operator maps $`L^3(\mathbb R^3)`$ to $`L^3(S^2)`$ with norm $`O_\varepsilon(\delta^{-\varepsilon})`$ for every ε &gt; 0. In four dimensions, every set containing a unit segment in every direction has Hausdorff dimension four.

- [The Kakeya maximal conjecture in three dimensions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Kakeya-maximal-conjecture-in-three-dimensions-September-23-2026/paper.pdf) -- no Lean statement
- [Every four-dimensional Kakeya set has full Hausdorff dimension](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Every-four-dimensional-Kakeya-set-has-full-Hausdorff-dimension-September-24-2026/paper.pdf) -- no Lean statement
## 075. The $`L\log L`$ Fourier-convergence conjecture

Proves that the ordinary symmetric Fourier partial sums of every complex-valued function in $`L\log L(\mathbb T)`$ converge almost everywhere along the full sequence. This resolves the classical sufficiency conjecture at the $`L\log L`$ scale. ([Lean](lean/docs/075.md))

- [Almost-everywhere Fourier convergence in L log L](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Almost-everywhere-Fourier-convergence-in-L-log-L-September-23-2026/paper.pdf) -- formalized: `FourierLLogL`
## 076. Real ultraflat Littlewood polynomials and unbounded binary merit factors

Constructs polynomials with N consecutive coefficients in $`\{-1,1\}`$ whose modulus is $`(1+o(1))\sqrt N`$ uniformly on the entire unit circle, for every sufficiently large integer length N. Thus real Littlewood polynomials are ultraflat, including at the real endpoints. Their binary merit factors tend to infinity, disproving Turyn's bounded-merit-factor conjecture. ([Lean](lean/docs/076.md))

- [Ultraflat real Littlewood polynomials](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ultraflat-real-Littlewood-polynomials-October-5-2026/ultraflat-real-littlewood-polynomials.pdf) -- no Lean statement
- [Nearly minimal maxima and positive minima of Littlewood polynomials](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Nearly-minimal-maxima-and-positive-minima-of-Littlewood-polynomials-October-5-2026/littlewood-lower-envelope.pdf) -- no Lean statement
- [Asymptotically minimal maxima of real Littlewood polynomials](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Asymptotically-minimal-maxima-of-real-Littlewood-polynomials-September-23-2026/paper.pdf) -- formalized: `AsymptoticallyMinimalLittlewood`, `LittlewoodFiniteFlatness`
## 077. Fourier restriction for positively curved surfaces

Proves the diagonal Fourier extension conjecture for positively curved surfaces in three dimensions. For every compact smooth positively curved surface $`\Sigma\subset\mathbb R^3`$, including surfaces with boundary, the extension operator is bounded from $`L^p(\Sigma)`$ to $`L^p(\mathbb R^3)`$ for every p &gt; 3.

- [Elliptic capacity propagation and Fourier restriction to the sphere](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Elliptic-capacity-propagation-and-Fourier-restriction-to-the-sphere-September-24-2026/Elliptic-capacity-propagation-and-Fourier-restriction-to-the-sphere-September-24-2026.pdf) -- no Lean statement
- [Diagonal Fourier extension for positively curved surfaces in three dimensions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Diagonal-Fourier-extension-for-positively-curved-surfaces-in-three-dimensions-September-24-2026/Diagonal-Fourier-extension-for-positively-curved-surfaces-in-three-dimensions-September-24-2026.pdf) -- no Lean statement
## 078. The three-dimensional Bochner–Riesz conjecture

Resolves the three-dimensional Bochner–Riesz conjecture in its strict range: the Bochner–Riesz multipliers of order δ are bounded on $`L^p(\mathbb R^3)`$ for every $`1\le p\le\infty`$ whenever $`\delta\gt \max\{3|1/p-1/2|-1/2,0\}`$.

- [Bochner–Riesz multipliers in three dimensions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Bochner-Riesz-Multipliers-in-Three-Dimensions-September-24-2026/Bochner-Riesz-Multipliers-in-Three-Dimensions-September-24-2026.pdf) -- no Lean statement
## 079. Local smoothing in three dimensions

Resolves Sogge's local smoothing conjecture for the Euclidean wave equation in three spatial dimensions. The estimate holds throughout the full strict range $`2\lt p\lt \infty`$, with Sobolev regularity above $`\max\{0,1-3/p\}`$. In particular, the critical L3 estimate holds with every positive Sobolev loss.

- [Critical local smoothing for the three-dimensional wave equation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Critical-local-smoothing-for-the-three-dimensional-wave-equation-September-24-2026/paper.pdf) -- no Lean statement
## 080. The exact Sobolev endpoint for Schrödinger convergence

Proves almost-everywhere convergence $`e^{it\Delta}f\to f`$ as $`t\downarrow0`$ for every $`f\in H^{n/(2(n+1))}(\mathbb R^n)`$ and every dimension n ≥ 2. This attains the sharp Sobolev equality case of Carleson's Schrödinger convergence problem, including the planar endpoint H1/3.

- [Endpoint convergence for the planar Schrodinger equation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Endpoint-convergence-for-the-planar-Schrodinger-equation-September-24-2026/paper.pdf) -- no Lean statement
- [Endpoint pointwise convergence for the Schrodinger equation in higher dimensions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Endpoint-pointwise-convergence-for-the-Schrodinger-equation-in-higher-dimensions-September-24-2026/paper.pdf) -- no Lean statement
## 081. Riesz transforms and rectifiability in higher codimension

Resolves the remaining higher-codimension Riesz-transform rectifiability problem: for d ≥ 4 and $`2\le n\le d-2`$, an n-Ahlfors–David regular Radon measure on ℝd is uniformly n-rectifiable whenever its n-dimensional Riesz transform is uniformly L2-bounded over all positive hard truncations. The rectifiability bounds depend only on dimension, regularity and operator bounds. ([Lean](lean/docs/081.md))

- [Riesz transforms and uniform rectifiability in higher codimension](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf) -- formalized: `RieszQuantitative`
## 082. Annular variation and dyadic absolute bounds for the triangular Hilbert transform

Proves maximal and annular r-variation bounds, for every r &gt; 2, from complex $`L^3(\mathbb R^2)\times L^3(\mathbb R^2)`$ to $`L^{3/2}(\mathbb R^2)`$. The maximal estimate controls both hard truncation endpoints and gives almost-everywhere and norm convergence. Pairing with a third input settles the triangular Hilbert transform estimate at the symmetric $`L^3\times L^3\times L^3`$ point. ([Lean](lean/docs/082.md))

- [Annular variation of the triangular Hilbert transform at the symmetric point](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Annular-variation-of-the-triangular-Hilbert-transform-at-the-symmetric-point-October-5-2026/annular-variation.pdf) -- no Lean statement
- [An L³ bound for the dyadic triangular Hilbert form](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-L3-bound-for-the-dyadic-triangular-Hilbert-form-October-5-2026/dyadic-triangular-hilbert.pdf) -- no Lean statement
- [The maximal triangular Hilbert transform at the symmetric point](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-maximal-triangular-Hilbert-transform-at-the-symmetric-point-September-24-2026/paper.pdf) -- formalized: `TriangularHilbert`
## 083. Hilbert transforms along Lipschitz directions

Proves a uniform strong L2 bound for the planar Hilbert transform along any Lipschitz unit vector field, at integration lengths bounded by an absolute multiple of its reciprocal Lipschitz constant. The estimate is uniform over inner truncations and yields an L2-bounded principal-value operator, establishing Stein's weak-type conjecture at this short scale. ([Lean](lean/docs/083.md))

- [A uniform Hilbert transform estimate for Lipschitz directions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf) -- formalized: `LipschitzHilbert`
## 084. The geometric case of the Erdős similarity conjecture

For every fixed $`q\in(0,1)`$, constructs compact subsets of $`[0,1]`$ with measure arbitrarily close to one containing no translated and nontrivially dilated copy of $`\{q^n:n\ge1\}`$, with dilations of either sign. This resolves the geometric-progression case of the Erdős similarity conjecture for every ratio. ([Lean](lean/docs/084.md))

- [The geometric case of the Erdős similarity conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026/geometric-erdos-similarity.pdf) -- no Lean statement
- [The dyadic case of the Erdős similarity conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-dyadic-case-of-the-Erdos-similarity-conjecture-September-25-2026/paper.pdf) -- formalized: `DyadicAvoidance`
## 085. Endpoint Sobolev regularity of centered disk averages

Resolves the planar centered-disk case of the Hajłasz–Onninen maximal-function regularity problem. For every real $`f\in W^{1,1}(\mathbb R^2)`$, the centered disk maximal function satisfies $`\|\nabla Mf\|_1\le C\|\nabla f\|_1`$ with an absolute constant. It belongs locally to $`W^{1,1}`$ and has a globally integrable weak gradient. ([Lean](lean/docs/085.md))

- [An Endpoint Gradient Bound for the Centered Disk Maximal Operator](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-Endpoint-Gradient-Bound-for-the-Centered-Disk-Maximal-Operator-September-26-2026/article.pdf) -- formalized: `SignedFiniteBand`, `DiskMaximal`
## 086. An <i>L</i><sup>3</sup> bound for the trilinear Hilbert transform

Proves that the principal-value trilinear Hilbert transform with shifts $`x-t`$, $`x-2t`$, $`x-3t`$ is bounded from $`L^3(\mathbb R)^3`$ to $`L^1(\mathbb R)`$. This resolves the L3 exponent case of the standard conjecture for slopes 1, 2, 3.

- [An <i>L</i><sup>3</sup> bound for the trilinear Hilbert transform](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-L3-bound-for-the-trilinear-Hilbert-transform-October-5-2026/paper.pdf) -- no Lean statement
## 087. The Mahler conjectures, functional inequalities and polar-product symplectic width

Resolves the symmetric and nonsymmetric geometric Mahler conjectures in every dimension, with Hanner polytopes and simplices as the respective volume-product minimizers and all equality cases classified. The corresponding sharp functional Mahler inequalities also hold. For n ≥ 2, every symmetric polar product $`K\times K^\circ`$ in dimension $`2n`$ has Gromov width 4. ([Lean](lean/docs/087.md))

- [The symmetric Mahler conjecture and its equality cases](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf) -- formalized: `MahlerConjecture`, `SymmetricMahlerEquality`, `GeneralMahler`, `SymmetricPolar`
- [The Mahler Conjecture for General Convex Bodies](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026/paper.pdf) -- formalized: `MahlerConjecture`, `SymmetricMahlerEquality`, `GeneralMahler`, `SymmetricPolar`
- [Symplectic Balls in Symmetric Polar Products](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Symplectic-Balls-in-Symmetric-Polar-Products-September-22-2026/paper.pdf) -- formalized: `MahlerConjecture`, `SymmetricMahlerEquality`, `GeneralMahler`, `SymmetricPolar`
## 088. Sharp projection-body inequalities and a counterexample to simplex maximization

Proves Petty's projection-volume conjecture in the remaining dimensions n ≥ 4: ellipsoids uniquely minimize projection-body volume at fixed body volume. Also establishes the full Lutwak–Petty projection inequalities. In contrast, products of simplices exceed Brannen's proposed simplex maximum for normalized projection-body volume by an exponential factor in every sufficiently large dimension. ([Lean](lean/docs/088.md))

- [Petty’s projection-volume conjecture in dimensions at least four](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Pettys-projection-volume-conjecture-in-dimensions-at-least-four-September-24-2026/paper.pdf) -- formalized: `PettyProjectionVolume`, `ProjectionCounterexample`, `ProjectionVolume`
- [A product counterexample to the simplex maximum for projection-body volume](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-product-counterexample-to-the-simplex-maximum-for-projection-body-volume-September-24-2026/paper.pdf) -- formalized: `PettyProjectionVolume`, `ProjectionCounterexample`, `ProjectionVolume`
## 089. Bounded-distortion <i>L</i><sub>1</sub> embeddings of planar and bounded-treewidth graphs

Resolves the planar and bounded-treewidth cases of the Gupta–Newman–Rabinovich–Sinclair conjecture. Shortest-path metrics of finite connected graphs with arbitrary positive edge lengths embed into real L1 with universal distortion for planar graphs, and distortion depending only on treewidth for bounded-treewidth graphs. The corresponding multicommodity flow–cut gaps are uniformly bounded. ([Lean](lean/docs/089.md))

- [Planar Graph Metrics Embed into L1 with Constant Distortion](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Planar-Graph-Metrics-Embed-into-L1-with-Constant-Distortion-September-23-2026/paper.pdf) -- formalized: `PlanarL1`, `BoundedTreewidthL1`
- [L1 Embeddings of Graphs of Bounded Treewidth](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/L1-Embeddings-of-Graphs-of-Bounded-Treewidth-September-23-2026/paper.pdf) -- formalized: `PlanarL1`, `BoundedTreewidthL1`
## 090. Triangular-lattice optimality, long-range Riesz and Coulomb energies, and spherical logarithmic energy

Proves that the triangular lattice minimizes the lower limit of energy per particle for every nonnegative completely monotone potential of squared distance among locally finite planar configurations of centered-disk density one. It also minimizes unit-background renormalized Riesz energies for $`0\lt s\lt 2`$ and Coulomb energy, resolving Sandier–Serfaty and the two-dimensional Brauchart–Hardin–Saff conjecture on the linear term of optimal spherical logarithmic energy. ([Lean](lean/docs/090.md))

- [An atomic certificate for triangular-lattice universal optimality](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf) -- formalized: `AtomicGaussian`, `TriangularEnergy`, `TriangularGaussian`, `PlanarPacking`
- [Universal optimality of the triangular lattice](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Universal-optimality-of-the-triangular-lattice-September-23-2026/paper.pdf) -- no Lean statement
- [A sharp Fourier certificate for planar circle packing](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf) -- formalized: `AtomicGaussian`, `TriangularEnergy`, `TriangularGaussian`, `PlanarPacking`
- [Triangular minimality for planar Coulomb renormalized energy](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Triangular-minimality-for-planar-Coulomb-renormalized-energy-September-23-2026/paper.pdf) -- no Lean statement
## 091. Logarithmic and <i>L</i><sub><i>p</i></sub> Brunn–Minkowski inequalities and the B-conjecture

Proves the logarithmic Brunn–Minkowski inequality for origin-symmetric convex bodies in every dimension, and the scalar-dilation B-conjecture for all even log-concave Radon measures. For Lebesgue volume it also proves the additive Lp Brunn–Minkowski inequality for full-dimensional origin-symmetric convex bodies throughout $`0\lt p\lt 1`$. ([Lean](lean/docs/091.md))

- [The logarithmic Brunn–Minkowski conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/paper.pdf) -- formalized: `LogBrunnMinkowski`
## 092. The optimal order of convex-body covering density

Determines the optimal worst-case covering density as $`\Theta(n\log n)`$, for both lattice and unrestricted translative coverings. Every convex body in ℝn, n ≥ 2, admits a lattice covering of density at most $`Cn\log n`$; centrally symmetric examples in every sufficiently large dimension require at least $`cn\log n`$ even without the lattice restriction, for absolute $`c,C\gt 0`$. ([Lean](lean/docs/092.md))

- [A single-lattice covering bound of order n log n](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-single-lattice-covering-bound-of-order-n-log-n-September-23-2026/paper.pdf) -- formalized: `SingleLatticeCovering`, `CoveringDensity`
- [Translative covering densities of order n log n](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf) -- formalized: `SingleLatticeCovering`, `CoveringDensity`
## 093. Dimension-free logarithmic Sobolev inequality for subgaussian log-concave measures

Proves a dimension-free logarithmic Sobolev inequality for centered log-concave densities with uniformly subgaussian linear marginals, with constant bounded by a universal multiple of the squared linear subgaussian parameter.

- [A dimension-free logarithmic Sobolev inequality for subgaussian log-concave measures](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-dimension-free-logarithmic-Sobolev-inequality-for-subgaussian-log-concave-measures-September-23-2026/paper.pdf) -- no Lean statement
## 094. Subpolynomial dimension reduction in <i>L</i><sub><i>p</i></sub>

For every fixed $`1\lt p\lt \infty`$ and distortion D &gt; 1, every n-point subset of real Lp embeds into $`\ell_p^d`$ with distortion at most D and dimension $`d=n^{o(1)}`$, answering Naor's sublinear-dimension question for p ≠ 2. In contrast, exact embeddings require worst-case dimension $`\Theta(n^2)`$ when p ≠ 2. ([Lean](lean/docs/094.md))

- [Subpolynomial dimension reduction in Lp](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Subpolynomial-dimension-reduction-in-Lp-September-23-2026/paper.pdf) -- formalized: `SubpolynomialLp`
## 095. Hyperbolicity cones without semidefinite lifts

Disproves the Projected Lax conjecture: some hyperbolicity cones are not spectrahedral shadows. The examples admit no exact finite affine semidefinite lift, regardless of the number of auxiliary variables or the real coefficients used. This also disproves the generalized Lax conjecture that every hyperbolicity cone is spectrahedral. ([Lean](lean/docs/095.md))

- [Hyperbolicity Cones Without Semidefinite Lifts](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hyperbolicity-Cones-Without-Semidefinite-Lifts-October-5-2026/nonliftable-hyperbolicity.pdf) -- no Lean statement
- [A nonspectrahedral hyperbolicity cone](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Nonspectrahedral-Hyperbolicity-Cone-September-24-2026/nonspectrahedral-hyperbolicity-cone.pdf) -- formalized: `HyperbolicCones`
- [An Exact Semidefinite Lift of a Nonspectrahedral Hyperbolicity Cone](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-Exact-Semidefinite-Lift-of-a-Nonspectrahedral-Hyperbolicity-Cone-October-5-2026/Exact-Semidefinite-Lift-of-a-Nonspectrahedral-Hyperbolicity-Cone.pdf) -- no Lean statement
## 096. The Gaussian propeller conjecture in every dimension

Proves that the sum of squared Gaussian first moments of any finite measurable partition is at most $`9/(8\pi)`$. In dimension at least two, three planar sectors of angle $`2\pi/3`$, extended orthogonally, attain the bound. Combined with the separate Unique Games theorem, this proves NP-hardness of improving the loss factor $`(8\pi/9)(1-1/k)`$ for identity-target kernel clustering with fixed k ≥ 3 on rational centered positive semidefinite inputs. ([Lean](lean/docs/096.md))

- [The Gaussian propeller bound in every dimension](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/main.pdf) -- formalized: `GaussianPropeller`
## 097. The Euclidean Steinitz–Bergström bound

Proves that any finite sequence in the Euclidean unit ball of ℝd admits signs keeping every partial sum within $`C\sqrt d`$, independently of length. Consequently every zero-sum family can be reordered with the same bound on unsigned partial sums. A matching lower bound gives the optimal order $`S_2(d)=\Theta(\sqrt d)`$. ([Lean](lean/docs/097.md))

- [The Euclidean Steinitz–Bergström theorem](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026.pdf) -- formalized: `SteinitzBergstrom`
## 098. Compact counterexamples to bi-Lipschitz dimension reduction

Every infinite-dimensional real Banach space contains a compact doubling set that admits no bi-Lipschitz embedding into any finite-dimensional normed space. The doubling constant is universal. This answers the Lang–Plaut problem negatively, even for compact subsets of Hilbert space. ([Lean](lean/docs/098.md))

- [A doubling Hilbert subset with no finite-dimensional bi-Lipschitz embedding](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-doubling-Hilbert-subset-with-no-finite-dimensional-bi-Lipschitz-embedding-September-25-2026/main.pdf) -- formalized: `DoublingHilbert`, `CompactBanach`
## 099. The sharp exponential scale of edit-distance distortion

Determines the least distortion of embedding edit distance on words of length at most d into real ℓ1: it is $`\exp(\Theta(\sqrt{\log d\,\log\log d}))`$. Insertions, deletions and substitutions have unit cost. The constants are uniform over all finite alphabets with at least two symbols, even when the alphabet grows with d; binary words already force the lower bound. ([Lean](lean/docs/099.md))

- [Edit Distance in l1: Matching Bounds up to Constants in the Exponent](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Edit-Distance-in-l1-Matching-Bounds-up-to-Constants-in-the-Exponent-September-27-2026/paper.pdf) -- formalized: `EditDistance`, `FiniteCircle`, `BinaryEditLower`, `TreeEdit`
- [Finite-Circle Obstructions, Binary Codes, and Histogram Embeddings for Edit Distance](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-Circle-Obstructions-Binary-Codes-and-Histogram-Embeddings-for-Edit-Distance-September-27-2026/paper.pdf) -- formalized: `EditDistance`, `FiniteCircle`, `BinaryEditLower`, `TreeEdit`
- [Tree Constructions for the l1 Distortion of Binary Edit Distance](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Tree-Constructions-for-the-l1-Distortion-of-Binary-Edit-Distance-September-27-2026/paper.pdf) -- formalized: `EditDistance`, `FiniteCircle`, `BinaryEditLower`, `TreeEdit`
## 100. Cylinder coverings below the half-area bound

Covers the entire closed regular tetrahedron by finitely many cylinders with compact triangular perpendicular bases whose total area is less than half its smallest orthogonal projection area. This disproves Bang's half-area cylinder-covering bound and the stronger directionwise normalized conjecture in dimension three. ([Lean](lean/docs/100.md))

- [Finite angular cylinder covers below the half-area bound](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-angular-cylinder-covers-below-the-half-area-bound-September-27-2026/main.pdf) -- formalized: `CylinderCovering`, `TriangularCovering`, `RuledCovering`
- [Finite cylinder approximation of ruled sets](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-cylinder-approximation-of-ruled-sets-September-27-2026/main.pdf) -- formalized: `CylinderCovering`, `TriangularCovering`, `RuledCovering`
- [Slope-field perturbations of the two-cylinder covering](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Slope-field-perturbations-of-the-two-cylinder-covering-September-27-2026/main.pdf) -- formalized: `CylinderCovering`, `TriangularCovering`, `RuledCovering`
- [Finite triangular approximation of radial sweeps](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-triangular-approximation-of-radial-sweeps-September-27-2026/main.pdf) -- formalized: `CylinderCovering`, `TriangularCovering`, `RuledCovering`
## 101. The sharp simplex conjecture for isotropic constants

Proves that simplices uniquely maximize the isotropic constant among convex bodies in every dimension, resolving the strong isotropic constant conjecture. Also establishes the sharp entropy lower bound for log-concave probability densities, with equality precisely for invertible affine images of products of one-sided exponential laws.

- [A sharp entropy bound and the simplex inequality for isotropic constants](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-sharp-entropy-bound-and-the-simplex-inequality-for-isotropic-constants-October-5-2026/isotropic-simplex.pdf) -- no Lean statement
## 102. The Unique Games Conjecture and optimal approximation thresholds

Proves Khot's Unique Games Conjecture. Independent direct reductions also establish NP-hardness, on unweighted graphs, of approximation beyond the Goemans–Williamson ratio for Max-Cut, below factor two for Vertex Cover, and within any fixed constant factor for Min-UnCut and directed feedback vertex set. These direct proofs use established PCP and Label Cover hardness results. ([Lean](lean/docs/102.md))

- [The Unique Games Theorem](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf) -- formalized: `UniqueGamesTheorem`, `OptimalMaxCut`, `VertexCover`, `MinUncut`, `DirectedFeedback`
- [A Direct Proof of Optimal Max-Cut Hardness](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf) -- formalized: `UniqueGamesTheorem`, `OptimalMaxCut`, `VertexCover`, `MinUncut`, `DirectedFeedback`
- [The Factor-Two Hardness Threshold for Vertex Cover](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf) -- formalized: `UniqueGamesTheorem`, `OptimalMaxCut`, `VertexCover`, `MinUncut`, `DirectedFeedback`
- [Constant-factor hardness of Min-UnCut](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf) -- formalized: `UniqueGamesTheorem`, `OptimalMaxCut`, `VertexCover`, `MinUncut`, `DirectedFeedback`
- [Constant-factor hardness of directed feedback vertex set](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf) -- formalized: `UniqueGamesTheorem`, `OptimalMaxCut`, `VertexCover`, `MinUncut`, `DirectedFeedback`
## 103. Exact derandomization of logarithmic space: $`\mathsf L=\mathsf{RL}=\mathsf{BPL}`$

Proves $`\mathsf L=\mathsf{RL}=\mathsf{BPL}`$, resolving derandomization for bounded-error logarithmic-space computation. An effective compiler converts each randomized polynomial-time logarithmic-space machine deciding a language with one-sided or two-sided error into a deterministic logarithmic-space decider with explicit polynomial running-time bounds. ([Lean](lean/docs/103.md))

- [Exact derandomization of logarithmic space: L = RL = BPL](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Derandomization-of-Logarithmic-Space-L-equals-RL-equals-BPL-September-23-2026/paper.pdf) -- formalized: `LogspaceEquality`
## 104. Quasipolynomial algorithms for mean-payoff, stochastic and parity games

Gives deterministic algorithms using $`2^{O((\log(L+2))^2)}`$ bit operations, for complete binary input length L, for ordinary mean-payoff games and two separate extensions. They compute exact values and optimal positional strategies in ordinary games, the nonnegative expectation-of-liminf value set in turn-based stochastic games, and the winning set for nonnegative liminf mean payoff conjoined with parity. Signed rewards, rational chance probabilities, and parity priorities are unrestricted and binary-encoded. ([Lean](lean/docs/104.md))

- [Turn-Based Stochastic Mean-Payoff Games in Deterministic Quasipolynomial Time](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Turn-Based-Stochastic-Mean-Payoff-Games-in-Deterministic-Quasipolynomial-Time-October-5-2026/stochastic-mean-payoff-games.pdf) -- no Lean statement
- [Mean-payoff parity games in quasipolynomial time](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Mean-payoff-parity-games-in-quasipolynomial-time-October-5-2026/mean-payoff-parity.pdf) -- no Lean statement
- [Deterministic quasipolynomial-time mean-payoff games](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Deterministic-quasipolynomial-time-mean-payoff-games-September-25-2026/paper.pdf) -- formalized: `TruffetCounterexample`, `RandomizedMeanPayoff`
- [Randomized quasipolynomial-time mean-payoff games](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Randomized-quasipolynomial-time-mean-payoff-games-September-25-2026/paper.pdf) -- formalized: `TruffetCounterexample`, `RandomizedMeanPayoff`
## 105. Perfect completeness for 2-to-1 games

Proves Khot's 2-to-1 Games Conjecture with perfect completeness: for every fixed rational $`\delta\in(0,1)`$, it is NP-hard to distinguish satisfiable games from games whose optimum is at most δ, on explicit unweighted instances. The alphabet depends only on δ, and every right-hand label has exactly two preimages under each constraint map. ([Lean](lean/docs/105.md))

- [Perfect completeness for 2-to-1 games](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf) -- formalized: `PerfectCompleteness`
## 106. Hardness of coloring three-colorable graphs

It is NP-hard to color a three-colorable graph using any fixed number c ≥ 3 of colors. More strongly, for every fixed $`0\lt \delta\lt 1/3`$, a deterministic polynomial-time reduction from 3SAT produces simple unweighted graphs that are three-colorable in the satisfiable case and have no independent set of size $`\delta n`$ otherwise, where n is the number of vertices. ([Lean](lean/docs/106.md))

- [Hardness of finding large independent sets in three-colorable graphs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026.pdf) -- formalized: `IndependentSets`
## 107. Matrix multiplication with exponent at most 9/4

Proves $`\omega\le9/4`$ over ℂ, giving $`O_\varepsilon(n^{9/4+\varepsilon})`$ arithmetic operations for square matrix multiplication. In characteristic zero, some inner dimension na with a &gt; 0.465 permits $`n^{2+o(1)}`$ rectangular multiplication. Further square bounds give ω &lt; 2.258 outside finitely many positive characteristics and ω &lt; 2.371054886006746 over every fixed field. ([Lean](lean/docs/107.md))

- [An Upper Bound of 9/4 for the Matrix Multiplication Exponent](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/paper.pdf) -- no Lean statement
- [Complex Matrix Multiplication Below 2.258 and Rectangular Bounds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026/Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026.pdf) -- formalized: `MatrixMultiplication`, `MatrixFields`
- [Staggered extraction for exact matrix multiplication over every field](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf) -- formalized: `MatrixMultiplication`, `MatrixFields`
## 108. A cubic permanent–determinant lower bound

Proves an $`\Omega(n^3)`$ lower bound for the border determinantal complexity of the $`n\times n`$ permanent over ℂ. Even coefficientwise limits of determinants of affine-linear matrices require matrix size at least $`cn^3`$, for an absolute c &gt; 0 and all sufficiently large n; the same bound therefore holds for exact representations. ([Lean](lean/docs/108.md))

- [A cubic lower bound for border determinantal complexity of the permanent](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026.pdf) -- formalized: `PermanentCubic`, `SmoothInitialForm`
## 109. Integer multiplication below $`n\log n`$

Multiplies two n-bit integers exactly at every input length in deterministic worst-case time $`O(n(\log n)^{1-\kappa})`$, with $`\kappa=2^{-182}`$, on one fixed finite-alphabet Turing machine with finitely many one-dimensional tapes. This disproves the Schönhage–Strassen $`n\log n`$ optimality conjecture in the ordinary multitape bit model.

- [Integer multiplication below n log n](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Integer-multiplication-below-n-log-n-September-23-2026/paper.pdf) -- no Lean statement
## 110. Optimal-order randomized <i>k</i>-server on arbitrary metrics

Establishes a randomized competitive ratio $`O(\log^2(k+1))`$ for k-server on every metric space, matching the worst-case lower-bound order. One policy serves every finite oblivious request sequence, including on infinite unbounded metrics. On finite rational metrics, a uniform implementation has polynomial preprocessing and per-request bit cost in the input length and $`\log(t+1)`$ at request t, with a finite instance-dependent additive movement constant. ([Lean](lean/docs/110.md))

- [Squared-logarithmic randomized k-server on arbitrary metrics](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Squared-logarithmic-randomized-k-server-on-arbitrary-metrics-September-24-2026/Squared-logarithmic-randomized-k-server-on-arbitrary-metrics-September-24-2026.pdf) -- formalized: `KServer`, `UniformKServer`
- [Uniform computation of the squared-logarithmic k-server bound](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf) -- formalized: `KServer`, `UniformKServer`
## 111. One-sample matroid prophet inequalities against an almighty adversary

For every finite matroid known in advance, gives a distribution-independent online rule using one independent sample per element and earning a universal constant fraction of the expected offline optimum. Values are independent and nonnegative, with finite expected optimum. The guarantee holds even when the arrival-order adversary sees all samples, values, and the rule's entire random seed; no polynomial-time implementation is asserted. ([Lean](lean/docs/111.md))

- [One Sample Suffices for Matroid Prophet Inequalities against an Almighty Adversary](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/One-Sample-Suffices-for-Matroid-Prophet-Inequalities-against-an-Almighty-Adversary-September-23-2026/final.pdf) -- formalized: `MatroidProphet`, `MatroidSecretary`
## 112. Beyond the square-root exponent for depth-three circuits

Constructs a single language in deterministic polynomial time whose n-bit membership function requires $`2^{\omega(\sqrt n)}`$ total gates in unbounded-fan-in OR–AND–OR circuits, at every sufficiently large input length. This crosses the square-root-exponent threshold for explicit depth-three Boolean circuit lower bounds. ([Lean](lean/docs/112.md))

- [Beyond the Square-Root Exponent for Depth-Three Boolean Circuits](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Beyond-the-Square-Root-Exponent-for-Depth-Three-Boolean-Circuits-September-23-2026/main.pdf) -- formalized: `DepthThree`
## 113. Approximate counting and entropy of perfect matchings

Gives a fully polynomial randomized approximation scheme for counting perfect matchings in arbitrary finite simple graphs, with exact detection of zero counts. Also proves the perfect-matching entropy conjecture of Anari, Oveis Gharan, and Vinzant, bounding the maximum entropy of a matching law at every feasible edge-marginal vector in a loopless labelled multigraph, including boundary points. ([Lean](lean/docs/113.md))

- [A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf) -- formalized: `MatchingFPRAS`, `MatchingEntropy`, `BinaryMatching`, `SingletonLoopMatching`, `MatchingEntropyBounds`, `TriangleFace`
- [Entropy and Face Dimension of the Perfect-Matching Polytope](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Entropy-and-Face-Dimension-of-the-Perfect-Matching-Polytope-September-23-2026/main.pdf) -- formalized: `MatchingFPRAS`, `MatchingEntropy`, `BinaryMatching`, `SingletonLoopMatching`, `MatchingEntropyBounds`, `TriangleFace`
## 114. Approximate counting of common integer polymatroid bases

Gives a fully polynomial randomized approximation scheme for counting common integer bases of two integral polymatroids of equal total rank, supplied by exact rank-value oracles. Capacities are binary-encoded, each integer vector counts once, and oracle calls and bit operations outside the oracles are polynomial on every execution. For matroids presented by independence oracles, the results also cover common independent sets of prescribed, unrestricted, or maximum cardinality, even when the ranks differ. ([Lean](lean/docs/114.md))

- [An FPRAS for Common Integer Polymatroid Bases with Binary Capacities](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Common-Integer-Polymatroid-Bases-with-Binary-Capacities-October-5-2026/polymatroid-fpras.pdf) -- no Lean statement
- [Approximate counting of common bases of two matroids](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Approximate-counting-of-common-bases-of-two-matroids-September-23-2026/main.pdf) -- formalized: `CommonBasesFPRAS`
## 115. Sampling and counting contingency tables with arbitrary margins

For nonnegative integer matrices with prescribed row and column sums, gives exact uniform sampling in expected polynomial bit time and almost-uniform sampling in worst-case polynomial bit time. The dimensions and binary-encoded margins are unrestricted. Also gives a fully polynomial randomized approximation scheme for counting such tables with arbitrary individual cell bounds, including structural zeros, with polynomial cost on every execution. ([Lean](lean/docs/115.md))

- [Exact Uniform Sampling of Contingency Tables with Arbitrary Margins](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf) -- formalized: `ContingencyTables`
- [An FPRAS for Cell-Bounded Contingency Tables](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/main.pdf) -- formalized: `ContingencyTables`
## 116. Uniform black-box noncommutative identity testing across characteristics

For each characteristic, constructs in deterministic polynomial bit time a polynomial-dimensional matrix tuple detecting every nonzero division-free noncommutative formula of bounded size over any field of that characteristic. Rational formulas over ℚ also admit polynomial-size hitting lists whenever they have a defined rational-matrix evaluation. ([Lean](lean/docs/116.md))

- [Uniform Matrix Hitting Points in Every Positive Characteristic](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Matrix-Hitting-Points-in-Every-Positive-Characteristic-October-4-2026/uniform-matrix-hitting-points-positive-characteristic.pdf) -- no Lean statement
- [One Rational Matrix Hitting Point for Noncommutative Formulas](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/One-Rational-Matrix-Hitting-Point-for-Noncommutative-Formulas-September-24-2026/One-Rational-Matrix-Hitting-Point-for-Noncommutative-Formulas-September-24-2026.pdf) -- formalized: `FormulaHitting`, `RationalHitting`
- [Polynomial Hitting Lists for Noncommutative Rational Formulas](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026.pdf) -- formalized: `FormulaHitting`, `RationalHitting`
## 117. Uniform sparsest cut: hardness and semidefinite gaps

Proves that approximating Uniform Sparsest Cut within any fixed constant factor is NP-hard, even with nonnegative rational capacities and unit demands. The Goemans–Linial semidefinite relaxation also has integrality gaps of order at least $`\sqrt{\log n}/(\log\log n)^3`$, approaching the square-root-logarithmic upper bound. ([Lean](lean/docs/117.md))

- [Constant-factor hardness of uniform sparsest cut](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Constant-factor-hardness-of-uniform-sparsest-cut-September-24-2026/Constant-factor-hardness-of-uniform-sparsest-cut-September-24-2026.pdf) -- no Lean statement
- [Near-square-root logarithmic integrality gaps for uniform sparsest cut](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Near-square-root-logarithmic-integrality-gaps-for-uniform-sparsest-cut-September-24-2026/Near-square-root-logarithmic-integrality-gaps-for-uniform-sparsest-cut-September-24-2026.pdf) -- formalized: `UniformSparsestCut`
## 118. Bin packing and unbounded configuration-LP gaps

Disproves the modified integer round-up conjecture of Scheithauer and Terno: the integral bin-packing optimum can exceed its configuration linear-programming value by an arbitrarily large additive constant. Approximating the optimum within any fixed additive constant is also NP-hard, even when every item exceeds 1/6 and each bin holds at most five items. ([Lean](lean/docs/118.md))

- [Additive hardness and unbounded configuration gaps in bin packing](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf) -- formalized: `BinPackingGap`
## 119. The Courtade–Kumar and Hellinger conjectures

Proves the Courtade–Kumar conjecture: among Boolean functions of independent uniform bits, a single coordinate retains the most mutual information after independent bit-flip noise. A stronger theorem treats randomized binary summaries at fixed initial information. The Hellinger conjecture is also proved for every Boolean output bias and noise correlation. ([Lean](lean/docs/119.md))

- [Sharp binary-information contraction on the discrete cube](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/main.pdf) -- formalized: `CourtadeKumar`, `SoftChannel204`
- [Hellinger contraction with arbitrary Boolean output bias](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hellinger-contraction-with-arbitrary-Boolean-output-bias-September-24-2026/main.pdf) -- no Lean statement
## 120. Almost-linear-time exact matching and prescribed-degree factors in general graphs

Gives a randomized algorithm finding an exact maximum-cardinality matching in any simple undirected graph in $`(n+m)^{1+o(1)}`$ word time, with success probability at least 2/3. The time bound holds on every computation path. The same guarantees apply to finding a spanning subgraph with prescribed admissible vertex degrees, or deciding that none exists.

- [Almost-Linear-Time Maximum-Cardinality Matching in General Graphs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Almost-Linear-Time-Maximum-Cardinality-Matching-in-Sparse-General-Graphs-September-24-2026/main.pdf) -- no Lean statement
## 121. Almost-linear approximation of edit distance

For every fixed rational $`\varepsilon\in(0,1)`$, gives a randomized $`(1+\varepsilon)`$ approximation to unit-cost edit distance in worst-case expected time $`N^{1+o(1)}`$, with success probability at least 2/3. The strings have total length N and polynomially bounded integer symbols. This is an asymptotic guarantee at fixed accuracy. ([Lean](lean/docs/121.md))

- [An Almost-Linear Approximation Scheme for Edit Distance](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf) -- formalized: `EditApproximation`
## 122. Quantitative trace-reconstruction bounds with a uniform decoder

At every fixed deletion probability in $`(0,1)`$, reconstructing an arbitrary length-n binary string requires $`n^{\Omega(\log\log n)}`$ independent traces, ruling out polynomial-sample reconstruction. A uniform decoder achieves quasipolynomial sample and running-time bounds for known fixed rational retention probabilities. When the deletion probability is at most $`n^{-\varepsilon}`$ for fixed ε &gt; 0, both bounds become polynomial in the input and parameter encoding. ([Lean](lean/docs/122.md))

- [Uniform quasipolynomial-time trace reconstruction](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-quasipolynomial-time-trace-reconstruction-October-5-2026/uniform-trace-reconstruction.pdf) -- no Lean statement
- [A latest-anchor induction with spectrally compact masks for worst-case trace reconstruction](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-latest-anchor-induction-with-spectrally-compact-masks-for-worst-case-trace-reconstruction-October-5-2026/paper.pdf) -- no Lean statement
- [Quantitative lower bounds for trace reconstruction](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf) -- formalized: `TraceReconstruction`
## 124. Polynomial-time scheduling on three identical machines

Resolves the three-processor unit-job scheduling problem of Garey and Johnson: a deterministic polynomial-time algorithm minimizes makespan for nonpreemptive unit-length jobs with arbitrary precedence constraints on three identical parallel machines. For an explicitly given precedence graph, it decides deadline feasibility exactly and constructs a feasible schedule. ([Lean](lean/docs/124.md))

- [A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-polynomial-time-algorithm-for-three-machine-unit-job-scheduling-September-24-2026/paper.pdf) -- formalized: `ThreeMachine`
## 125. The metric <i>k</i>-median approximation threshold and recovery

Gives a deterministic polynomial-time $`(1+2/e+\varepsilon)`$-approximation for finite rational metric k-median with specified candidate facilities, for every fixed ε &gt; 0. Assuming $`P\ne NP`$, the optimal infimum approximation factor is $`1+2/e`$. ([Lean](lean/docs/125.md))

- [Single-exponential recovery and bounded-price strictness for metric k-median](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf) -- formalized: `KMedianRecovery`, `KMedianRefinedRecovery`, `KMedianThreshold`, `MetricKMedian`
- [The approximation threshold for metric k-median](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf) -- formalized: `KMedianRecovery`, `KMedianRefinedRecovery`, `KMedianThreshold`, `MetricKMedian`
## 126. Exponential semidefinite complexity of perfect matching

Proves that every exact semidefinite lift of the perfect matching polytope has exponential size, answering Rothvoss's polynomial-size lift question negatively. The bound holds even for the positive semidefinite rank of its odd-cut slack matrix after any fixed shift $`0\lt \rho\lt 1`$, allowing arbitrary real positive semidefinite factors. ([Lean](lean/docs/126.md))

- [Exponential PSD rank of positively shifted matching matrices](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exponential-PSD-rank-of-positively-shifted-matching-matrices-October-5-2026/shifted-matching-psd.pdf) -- formalized: `MatchingAffineLift`, `MatchingPSD`
## 127. Average sensitivity of polynomial threshold functions

Proves that a degree-at-most-d polynomial threshold function on the uniform n-dimensional Boolean cube has average sensitivity at most $`8d\sqrt n`$, uniformly for $`1\le d\le n`$. Average sensitivity counts expected output changes under single-bit flips. This establishes the asymptotic Gotsman–Linial conjecture, allowing polynomial zeros with $`\mathop{\mathrm{sign}}\nolimits (0)=1`$. ([Lean](lean/docs/127.md))

- [Average sensitivity of polynomial threshold functions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Average-Sensitivity-of-Polynomial-Threshold-Functions-September-25-2026/main.pdf) -- formalized: `GotsmanLinial`
## 128. A factor-two approximation for shortest common superstring

Gives a deterministic polynomial-time algorithm constructing a common superstring of length at most twice the optimum for every finite family of explicitly represented strings. The running time is polynomial in the full encoded input length, including symbol labels. ([Lean](lean/docs/128.md))

- [A Polynomial-Time 2-Approximation for Shortest Common Superstring](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Polynomial-Time-2-Approximation-for-Shortest-Common-Superstring-September-24-2026/paper.pdf) -- formalized: `Superstring`
## 129. Exponential state costs for two-way automata

Proves exponential lower bounds both for complementing two-way nondeterministic finite automata and for simulating one-way nondeterministic automata by two-way deterministic ones. The latter resolves the Sakoda–Sipser state-succinctness conjecture over growing finite alphabets; both results rule out polynomial state bounds independent of alphabet size. ([Lean](lean/docs/129.md))

- [An exponential state lower bound for two-way nondeterministic complementation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-exponential-state-lower-bound-for-two-way-nondeterministic-complementation-September-25-2026/paper.pdf) -- formalized: `TwoWayComplementation`, `TwoWayDeterminization`, `OneWayLiveness`
- [An exponential two-way deterministic state lower bound for one-way liveness](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-exponential-two-way-deterministic-state-lower-bound-for-one-way-liveness-September-25-2026/main.pdf) -- formalized: `TwoWayComplementation`, `TwoWayDeterminization`, `OneWayLiveness`
## 130. Exact Fourier transforms below $`n\log n`$

Gives a deterministic length-n discrete Fourier transform algorithm using $`O(n(\log n)^{1-\delta})`$ operations for every n, with explicit $`\delta=10^{-13}`$. The model uses exact complex arithmetic, unrestricted coefficients and a supplied root of unity, and counts scalar preparation and logarithmic-word indexing. ([Lean](lean/docs/130.md))

- [An explicit power saving for the exact discrete Fourier transform](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf) -- formalized: `ExactFourier`, `UniformFourier`
- [Finite tensor savings and exact Fourier circuits](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026/main.pdf) -- formalized: `ExactFourier`, `UniformFourier`
## 131. Rapid mixing of graph switches for every degree sequence

Resolves the simple-undirected Kannan–Tetali–Vempala conjecture: the lazy edge-switch chain mixes in $`O(n^8)`$ time for every graphical labeled degree sequence. The same degree-constrained graphs can also be sampled exactly uniformly by an almost-surely terminating algorithm with expected polynomial bit running time. ([Lean](lean/docs/131.md))

- [Polynomial mixing of the switch chain for every graphical degree sequence](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026/main.pdf) -- formalized: `SwitchChain`
## 132. A superquadratic separation of sensitivity and block sensitivity

Constructs total Boolean functions with block sensitivity $`\mathop{\mathrm{bs}}\nolimits (f)\ge s(f)^\alpha`$ for a fixed α &gt; 2, disproving the quadratic strengthening of the Sensitivity Conjecture. Here $`s(f)`$ counts influential individual-bit flips, while block sensitivity allows disjoint groups of bits to change together. ([Lean](lean/docs/132.md))

- [A superquadratic separation between sensitivity and block sensitivity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/paper.pdf) -- formalized: `SensitivitySeparation`
## 133. The computational complexity of Weisfeiler–Leman refinement

Proves unconditional $`n^{\Omega(k)}`$ deterministic time lower bounds for joint and separate k-dimensional Weisfeiler–Leman equivalence, for sufficiently large fixed k in the specified sequential adjacency-matrix models. With dimension as input, joint equivalence is EXPTIME-complete even on subcubic graphs; deciding whether refinement identifies a graph is also EXPTIME-complete. ([Lean](lean/docs/133.md))

- [Parity lifts and bounded-treewidth witnesses for Weisfeiler–Leman equivalence](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Parity-lifts-and-bounded-treewidth-witnesses-for-Weisfeiler-Leman-equivalence-September-25-2026/paper.pdf) -- formalized: `ParityLifts`, `WLIdentification`, `WeisfeilerLeman`, `VariableWL`
- [The complexity of identifying a graph by Weisfeiler–Leman refinement](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-complexity-of-identifying-a-graph-by-Weisfeiler-Leman-refinement-September-25-2026/paper.pdf) -- formalized: `ParityLifts`, `WLIdentification`, `WeisfeilerLeman`, `VariableWL`
- [Unconditional time lower bounds for Weisfeiler–Leman equivalence](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Unconditional-time-lower-bounds-for-Weisfeiler-Leman-equivalence-September-25-2026/paper.pdf) -- formalized: `ParityLifts`, `WLIdentification`, `WeisfeilerLeman`, `VariableWL`
- [Variable-dimension Weisfeiler–Leman equivalence on general and subcubic graphs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Variable-dimension-Weisfeiler-Leman-equivalence-on-general-and-subcubic-graphs-September-25-2026/paper.pdf) -- formalized: `ParityLifts`, `WLIdentification`, `WeisfeilerLeman`, `VariableWL`
## 134. Generalized star height at most three

Every regular language over a finite alphabet has a generalized regular expression with at most three nested Kleene stars, allowing union, concatenation and complement over the same alphabet. This establishes an absolute bound independent of automaton size, resolving the uniform-boundedness version of the generalized star-height problem. ([Lean](lean/docs/134.md))

- [Finite Monoid Computations and a Uniform Generalized Star-Height Bound](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-Monoid-Computations-and-a-Uniform-Generalized-Star-Height-Bound-September-25-2026/Finite-Monoid-Computations-and-a-Uniform-Generalized-Star-Height-Bound-September-25-2026.pdf) -- formalized: `GeneralizedStarHeight`
- [Generalized Star Height at Most Four](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Generalized-Star-Height-at-Most-Four-September-25-2026/Generalized-Star-Height-at-Most-Four-September-25-2026.pdf) -- formalized: `GeneralizedStarHeight`
- [Generalized Star Height at Most Three](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Generalized-Star-Height-at-Most-Three-September-25-2026/article.pdf) -- formalized: `GeneralizedStarHeight`
## 135. Homogeneous depth-five lower bounds for iterated matrix multiplication

Over every characteristic-zero field, the $`(1,1)`$ entry of a product of n independent $`n\times n`$ variable matrices requires $`n^{\Theta(\sqrt n)}`$ gates in homogeneous depth-five sum–product circuits. This sharp bound allows shared gates and bottom linear forms involving all variables. ([Lean](lean/docs/135.md))

- [Homogeneous depth-five lower bounds for iterated matrix multiplication](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Homogeneous-depth-five-lower-bounds-for-iterated-matrix-multiplication-September-25-2026/Homogeneous-depth-five-lower-bounds-for-iterated-matrix-multiplication-September-25-2026.pdf) -- formalized: `DepthFive`
## 136. A quasilinear PCP theorem for PPAD

Resolves the quasilinear PCP-for-PPAD conjecture. An End-of-Line instance of length N reduces to numerical circuit constraints of total length $`N(\log N)^{O(1)}`$ such that any polynomially encoded rational assignment satisfying all but a fixed fraction to fixed accuracy yields an endpoint solution. Such assignments always exist, giving robust local verification with only quasilinear size overhead.

- [The PCP-for-PPAD conjecture: a quasilinear reduction](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-PCP-for-PPAD-conjecture-a-quasilinear-reduction-September-25-2026/paper.pdf) -- no Lean statement
## 137. One-tape time simulation in two-fifths-power space

Determines the halting and finite-control outcome of a fixed deterministic one-writable-tape machine up to time T using $`O(T^{2/5}\log^C(T+2))`$ space, improving the square-root exponent. Heads move at most one cell per step; finitely many read-only input heads are allowed. Initial contents are independent of T, and contents and input symbols have polylogarithmic-space access. Simulation time is unrestricted. ([Lean](lean/docs/137.md))

- [Simulating One-Tape Time in Two-Fifths-Power Space](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Simulating-One-Tape-Time-in-Two-Fifths-Power-Space-September-25-2026/article.pdf) -- formalized: `OneTapeSpace`
## 138. Subset Sum in $`O(2^{0.49n})`$ time

Gives a uniform randomized classical algorithm for worst-case Subset Sum in ordinary $`O(2^{0.49n})`$ word-RAM time on polynomial-bit inputs, where n counts the integers. The time bound holds on every execution and success probability is at least 2/3 on every input. Inputs may repeat positive integers; words have $`O(n+b)`$ bits for maximum input bit length b.

- [Subset Sum in Time $`O(2^{0.49n})`$ ](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Subset-Sum-in-Time-2-power-0-49n-October-4-2026/subset-sum.pdf) -- no Lean statement
- [A Low-Space Algorithm for Worst-Case Subset Sum](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Low-Space-Algorithm-for-Worst-Case-Subset-Sum-September-26-2026/paper.pdf) -- no Lean statement
## 139. Subpolynomial query complexity for log-concave sampling

For C2 potentials with a supplied minimizer and $`I\preceq\nabla^2V\preceq2I`$, proves that sampling within total variation 1/10 requires only $`C_\varepsilon d^\varepsilon`$ exact value-and-gradient queries for every fixed ε &gt; 0. The bound holds on every run, with unrestricted computation between queries. A logarithmic lower bound also holds, so the optimal power-law exponent in this oracle model is zero. ([Lean](lean/docs/139.md))

- [Subpolynomial query complexity for well-conditioned log-concave sampling](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf) -- formalized: `LogConcaveQuery`
## 140. Memory–sample lower bounds for noiseless Gaussian regression

For fixed A &gt; 0, a one-pass learner with $`Ad^2`$ persistent bits needs $`\Omega_A(d\log(1/\epsilon))`$ noiseless Gaussian samples to recover a unit vector to angular error $`0\lt \epsilon\le1/10`$ with probability 2/3, uniformly in accuracy for large d. Computation and randomized updates are unrestricted, but output uses only the terminal state, stopping index and fresh randomness. ([Lean](lean/docs/140.md))

- [Memory and precision in noiseless Gaussian regression](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Memory-and-precision-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf) -- formalized: `MemoryPrecision`, `NoiselessRegression`, `PosteriorReplicas`, `GaussianFiniteEntropy`, `GaussianInformation`, `ProjectionMoments`, `GaussianReplacement`, `SubsphereCurrent`
- [Posterior replicas and conditional information in Gaussian regression](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf) -- formalized: `MemoryPrecision`, `NoiselessRegression`, `PosteriorReplicas`, `GaussianFiniteEntropy`, `GaussianInformation`, `ProjectionMoments`, `GaussianReplacement`, `SubsphereCurrent`
- [Localization costs and information growth for exact Gaussian observations](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf) -- formalized: `MemoryPrecision`, `NoiselessRegression`, `PosteriorReplicas`, `GaussianFiniteEntropy`, `GaussianInformation`, `ProjectionMoments`, `GaussianReplacement`, `SubsphereCurrent`
- [Projection moments, positive cap domination, and Riesz estimates on the sphere](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Projection-moments-positive-cap-domination-and-Riesz-estimates-on-the-sphere-September-27-2026/paper.pdf) -- formalized: `MemoryPrecision`, `NoiselessRegression`, `PosteriorReplicas`, `GaussianFiniteEntropy`, `GaussianInformation`, `ProjectionMoments`, `GaussianReplacement`, `SubsphereCurrent`
- [Replacing Gaussian observations in memory-constrained inference](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf) -- formalized: `MemoryPrecision`, `NoiselessRegression`, `PosteriorReplicas`, `GaussianFiniteEntropy`, `GaussianInformation`, `ProjectionMoments`, `GaussianReplacement`, `SubsphereCurrent`
- [Subsphere methods for memory-sample lower bounds in noiseless Gaussian regression](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Subsphere-methods-for-memory-sample-lower-bounds-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf) -- formalized: `MemoryPrecision`, `NoiselessRegression`, `PosteriorReplicas`, `GaussianFiniteEntropy`, `GaussianInformation`, `ProjectionMoments`, `GaussianReplacement`, `SubsphereCurrent`
## 141. Existential–universal real sentences in the counting hierarchy

Proves that the existential theory of the reals lies in the counting hierarchy. More generally, truth of existential–universal real sentences can be decided at one fixed level of that hierarchy, even when their integer polynomials are specified by arithmetic circuits.

- [Existential–universal real sentences in the counting hierarchy](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/etr-counting-hierarchy.pdf) -- no Lean statement
## 142. Deterministic polynomial factorization over prime fields

Gives a uniform deterministic algorithm that completely factors every nonzero dense degree-n polynomial over a prime field 𝔽p, including multiplicities, in bit complexity polynomial in $`(n+1)\log p`$. The prime is supplied in binary. No randomness, integer-factorization or primitive-root oracle, or GRH assumption is required.

- [Deterministic Polynomial Factorization over Prime Fields](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Deterministic-Polynomial-Factorization-over-Prime-Fields-October-4-2026/Deterministic-Polynomial-Factorization-over-Prime-Fields.pdf) -- no Lean statement
## 143. Hilbert's sixteenth problem: uniform bounds for limit cycles

Resolves the uniform boundedness assertion in Hilbert's sixteenth problem: the number of isolated periodic orbits of a real planar polynomial vector field is bounded by a finite constant depending only on its degree. For classical quintic Liénard systems, the exact maximum is two limit cycles. ([Lean](lean/docs/143.md))

- [Uniform bounds for planar polynomial limit cycles](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/uniform-bounds-for-planar-polynomial-limit-cycles-September-24-2026/uniform-bounds-for-planar-polynomial-limit-cycles-September-24-2026.pdf) -- no Lean statement
- [Two limit cycles for quintic Liénard systems](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/two-limit-cycles-for-quintic-lienard-systems-September-24-2026/two-limit-cycles-for-quintic-lienard-systems-September-24-2026.pdf) -- formalized: `QuinticLienard`
## 144. Banach’s simple Lebesgue-spectrum problem

Resolves the probability-preserving form of Banach's simple Lebesgue-spectrum problem within smooth dynamics. A smooth volume-preserving diffeomorphism of the standard-volume three-torus has simple Lebesgue spectrum on its entire complex mean-zero L2 space: the bilateral iterates of one real observable form an orthonormal basis of that space. ([Lean](lean/docs/144.md))

- [A smooth three-torus diffeomorphism with simple Lebesgue spectrum](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-smooth-three-torus-diffeomorphism-with-simple-Lebesgue-spectrum-September-23-2026/paper.pdf) -- formalized: `ThreeTorus`
## 145. Rokhlin’s multiple-mixing problem

Proves that every invertible mixing probability-preserving transformation is mixing of all finite orders, resolving Rokhlin's multiple-mixing problem for a single transformation. Correlations among any finite collection of measurable sets converge to the product of their measures whenever all pairwise time separations diverge. ([Lean](lean/docs/145.md))

- [Rokhlin's multiple-mixing problem for one transformation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf) -- formalized: `Rokhlin`
## 146. Positive metric entropy for the standard map

Proves that the standard sine map on the two-dimensional torus has positive metric entropy with respect to area for every sufficiently large positive parameter. This establishes Sinai's positive-parameter-measure conjecture for the original family, with the stronger conclusion of a full parameter tail. ([Lean](lean/docs/146.md))

- [Positive Metric Entropy for the Standard Map at Large Parameters](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf) -- formalized: `StandardMapComponents`, `StandardMapEntropy`, `StandardMapLyapunov`
## 147. The near-boundary Birkhoff conjecture

Resolves the near-boundary Birkhoff conjecture for smooth strictly convex planar billiards of positive curvature. Such a billiard is an ellipse whenever a full grazing annulus is continuously foliated by individually invariant essential curves. A continuous physical collar of smooth closed convex caustics also suffices.

- [Continuous Phase Foliations Create Analytic Caustic Collars](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Continuous-Phase-Foliations-Create-Analytic-Caustic-Collars-September-24-2026/paper.pdf) -- no Lean statement
- [Rigidity of Smooth Billiards with a Continuous Caustic Collar](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Rigidity-of-Smooth-Billiards-with-a-Continuous-Caustic-Collar-September-24-2026/paper.pdf) -- no Lean statement
## 148. The entropy-rate dimension formula for self-similar measures

For every self-similar measure on the line generated by finitely many contracting similarities, proves $`\dim_{\mathrm H}\mu=\min\{1,h_{\mathrm{RW}}/\chi\}`$, where $`h_{\mathrm{RW}}`$ is the entropy rate of random composed maps and χ the average logarithmic contraction. This resolves the entropy-rate dimension conjecture without a separation assumption, allowing exact overlaps and unequal contraction ratios. ([Lean](lean/docs/148.md))

- [The entropy-rate dimension formula for self-similar measures on the line](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-entropy-rate-dimension-formula-for-self-similar-measures-on-the-line-September-24-2026/main.pdf) -- formalized: `SelfSimilar`, `SelfSimilarCorollaries`
## 149. Classwise permanence for weakly reversible mass-action systems

Proves the permanence conjecture for every finite weakly reversible mass-action system with fixed positive rate constants. Every positive stoichiometric compatibility class, even an unbounded one, has a common compact convex forward-invariant absorbing set. All positive trajectories in that class therefore eventually share positive lower and finite upper concentration bounds. ([Lean](lean/docs/149.md))

- [Uniform Permanence in Weakly Reversible Mass-Action Systems](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Permanence-in-Weakly-Reversible-Mass-Action-Systems-October-5-2026/permanence.pdf) -- no Lean statement
- [Boundedness and persistence of weakly reversible mass-action systems](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Boundedness-and-persistence-of-weakly-reversible-mass-action-systems-September-25-2026/paper.pdf) -- formalized: `MassAction`
## 150. Weak mixing of triangular billiards with an irrational angle

Proves that the billiard flow in every nondegenerate Euclidean triangle with at least one angle irrational relative to π is weakly mixing for normalized area times uniform direction. This strengthens ergodicity on the entire irrational-angle class, with no genericity or Diophantine restrictions. ([Lean](lean/docs/150.md))

- [Weak mixing of triangular billiards with an irrational angle](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Weak-mixing-of-triangular-billiards-with-an-irrational-angle-October-5-2026/weak-mixing-triangular-billiards.pdf) -- no Lean statement
- [Ergodicity of triangular billiards with an irrational angle](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ergodicity-of-triangular-billiards-with-an-irrational-angle-September-25-2026/Ergodicity-of-triangular-billiards-with-an-irrational-angle-September-25-2026.pdf) -- formalized: `IrrationalTriangleBilliard`
## 151. A <i>C</i><sup>1</sup> counterexample to the entropy conjecture

Constructs a noninvertible C1 self-map of a compact smooth manifold with zero topological entropy but eigenvalue 2 on second homology. This disproves the homological entropy lower bound for general C1 self-maps: homological growth need not force positive orbit complexity. ([Lean](lean/docs/151.md))

- [A C^1 Counterexample to the Entropy Conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-C1-Counterexample-to-the-Entropy-Conjecture-September-25-2026/article.pdf) -- formalized: `C1EntropyCounterexample`
## 152. Zero entropy does not guarantee a smooth positive-volume model

Constructs a zero-entropy ergodic invertible transformation of a standard nonatomic probability space that is not measurably conjugate to any C∞ diffeomorphism preserving a strictly positive smooth probability density on a compact finite-dimensional manifold. One example rules out every finite dimension. ([Lean](lean/docs/152.md))

- [A zero-entropy system without a smooth positive-volume model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-finite-entropy-system-without-a-smooth-positive-volume-model-September-25-2026/paper.pdf) -- formalized: `SmoothObstruction`
## 153. Arithmetic classification and non-Pisot singularity for Bernoulli convolutions

Classifies singular and absolutely continuous unbiased Bernoulli convolutions for every $`\lambda\in(0,1)`$ by an infinite, one-sided approximation condition using explicit finite sets of algebraic units. It also proves singularity at reciprocals of every quartic Salem number in $`(1,2)`$, giving examples beyond reciprocal Pisot parameters.

- [Arithmetic classification and non-Pisot singularity for Bernoulli convolutions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Arithmetic-classification-and-non-Pisot-singularity-for-Bernoulli-convolutions-October-3-2026/paper.pdf) -- no Lean statement
## 154. Pointwise multiple ergodic averages for mixing transformations

Proves almost-everywhere convergence of consecutive multiple ergodic averages of every finite length for invertible mixing probability-preserving transformations. For each fixed tuple of bounded functions, the limit is the product of their integrals, along all positive averaging lengths. No mixing rate or standardness assumption on the probability space is required.

- [Pointwise Multiple Ergodic Averages for Mixing Transformations](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Pointwise-Multiple-Ergodic-Averages-for-Mixing-Transformations-October-4-2026/multiple-ergodic-averages.pdf) -- no Lean statement
- [Pointwise convergence of fourfold ergodic averages for mixing transformations](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Pointwise-convergence-of-fourfold-ergodic-averages-for-mixing-transformations-October-4-2026/fourfold-ergodic-averages.pdf) -- no Lean statement
- [Triple ergodic averages with distinct integer slopes](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Triple-ergodic-averages-with-distinct-integer-slopes-October-4-2026/triple-ergodic-distinct-slopes.pdf) -- no Lean statement
- [Pointwise convergence of triple ergodic averages for mixing transformations](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Pointwise-convergence-of-triple-ergodic-averages-for-mixing-transformations-October-4-2026/pointwise-triple-ergodic-averages-mixing-transformations.pdf) -- no Lean statement
## 155. A counterexample to periodic tiling in dimension three

Constructs a finite translational tile in ℤ3 that tiles space but admits no fully periodic tiling, disproving the periodic tiling conjecture in the smallest possible lattice dimension. Its unit-cube thickening gives the same counterexample in ℝ3, even with arbitrary real translation vectors. ([Lean](lean/docs/155.md))

- [A translational tile with no fully periodic tiling in dimension three](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-translational-tile-with-no-fully-periodic-tiling-in-dimension-three-September-23-2026/paper.pdf) -- formalized: `PeriodicTilingThree`
## 156. Borsuk's conjecture fails in dimension nine

Constructs a compact subset of ℝ9 that cannot be covered by ten sets of strictly smaller diameter, disproving Borsuk's covering assertion already in dimension nine. The example consists of rank-one orthogonal projectors onto lines in ℝ4, with the Frobenius metric. ([Lean](lean/docs/156.md))

- [A nine-dimensional counterexample to Borsuk's covering assertion](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf) -- formalized: `BorsukNine`
## 157. Graph coloring, clique minors, and Colin de Verdière invariants

Disproves Hadwiger's conjecture even for fractional coloring: arbitrarily large finite simple graphs with independence number at most two satisfy $`\chi_f(G)\gt h(G)`$, where $`h(G)`$ is the largest clique-minor order. Also disproves the fractional Colin de Verdière chromatic bound $`\chi_f(G)\le\mu(G)+1`$. In the positive direction, every finite nonempty graph satisfies $`\chi_{\mathrm{list}}(G)\le C h(G)`$ for a universal constant C. ([Lean](lean/docs/157.md))

- [A counterexample to Hadwiger's conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf) -- formalized: `ListHadwiger`, `HadwigerCounterexample`
- [A counterexample to the Colin de Verdière chromatic conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-the-Colin-de-Verdiere-chromatic-conjecture-September-23-2026/paper.pdf) -- no Lean statement
- [A linear list-coloring bound in terms of the Hadwiger number](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-linear-list-coloring-bound-in-terms-of-the-Hadwiger-number-September-23-2026/paper.pdf) -- formalized: `ListHadwiger`, `HadwigerCounterexample`
## 158. The Euclidean plane cannot be colored with five colors

Proves that every five-coloring of the Euclidean plane has a monochromatic pair at distance one, with no restriction on the color classes. This advances the Hadwiger–Nelson problem: together with the classical seven-coloring, only six and seven remain possible chromatic numbers of the plane. ([Lean](lean/docs/158.md))

- [The Euclidean plane is not five-colorable](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf) -- formalized: `EuclideanFiveColor`, `PlaneColoring`
## 159. Erdős’s reciprocal-sum conjecture and quasipolynomial Szemerédi bounds

Proves Erdős's conjecture that every set of positive integers with divergent reciprocal sum contains arithmetic progressions of every finite length. Quantitatively, for each fixed k ≥ 3, every subset of $`\{1,\ldots,N\}`$ with no nonconstant k-term progression has size at most $`C_kN\exp[-c_k(\log N)^{\varepsilon_k}]`$, with positive constants depending only on k. ([Lean](lean/docs/159.md))

- [Quasipolynomial Bounds for Arithmetic Progressions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf) -- formalized: `ErdosReciprocal`
## 160. Superexponential van der Waerden numbers

Resolves Erdős's superexponential-growth question for van der Waerden numbers. If $`W_r(k)`$ is the least interval length forcing a monochromatic k-term progression in every r-coloring, then $`W_r(k)\gt k^{ck\lfloor\log_2 r\rfloor}`$ for an absolute c &gt; 0, all r ≥ 2 and sufficiently large k, uniformly in r. In particular, $`W_r(k)^{1/k}\to\infty`$ for each fixed r. ([Lean](lean/docs/160.md))

- [Quantitative Superexponential Bounds for van der Waerden Numbers](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quantitative-Superexponential-Bounds-for-van-der-Waerden-Numbers-September-23-2026/paper.pdf) -- formalized: `QuantitativeVanDerWaerden`
## 161. Counterexamples to Sidorenko’s conjecture and the forcing conjecture

Disproves Sidorenko's conjecture with a connected bipartite pattern on 35 vertices and 66 edges that occurs less frequently than in a random graph of the same edge density. The same pattern disproves the forcing conjecture of Skokan and Thoma: matching its density and the edge density of a constant graphon need not force quasirandomness. ([Lean](lean/docs/161.md))

- [A counterexample to Sidorenko's conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/paper.pdf) -- formalized: `SidorenkoCounterexample`
## 162. Counterexamples to Ryser’s covering conjecture

Disproves Ryser's covering conjecture by constructing intersecting $`(q+1)`$-partite, $`(q+1)`$-uniform hypergraphs with covering number $`q+1`$, rather than the predicted bound q, for every sufficiently large prime q. A separate construction over extension fields also disproves Gyárfás's monochromatic tree-cover conjecture. ([Lean](lean/docs/162.md))

- [Balanced counterexamples to Ryser's conjecture at prime orders](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/paper.pdf) -- formalized: `BalancedRyser`, `RyserCovering`, `RyserOddExtensions`
- [A counterexample to Ryser's covering conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/paper.pdf) -- formalized: `BalancedRyser`, `RyserCovering`, `RyserOddExtensions`
## 164. Hindman’s finite sums and products conjecture

Proves Hindman's finite sums and products conjecture: every finite coloring of the positive integers contains sets of any prescribed finite size whose nonempty subset sums and nonempty subset products all have one common color.

- [Monochromatic finite sums and products in the positive integers](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/paper.pdf) -- no Lean statement
## 165. The Harary–Hill and Zarankiewicz crossing-number formulas

Resolves the Harary–Hill conjecture and Turán's brickyard problem in the Zarankiewicz formulation, determining the crossing numbers of every complete and complete bipartite graph. The result proves the optimality of the classical drawings among all plane drawings with continuous edge arcs. ([Lean](lean/docs/165.md))

- [The crossing number of complete graphs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-crossing-number-of-complete-graphs-September-23-2026/paper.pdf) -- formalized: `CompleteCrossing`, `BipartiteCrossing`
- [The crossing number of complete bipartite graphs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf) -- formalized: `CompleteCrossing`, `BipartiteCrossing`
## 166. The higher-dimensional Erdős distinct-distances conjecture

For every fixed d ≥ 3, any n ≥ 2 distinct points in ℝd determine at least $`c_dn^{2/d}`$ distinct distances, with $`c_d\gt 0`$ depending only on dimension. This matches the integer-grid order and resolves the higher-dimensional Erdős distinct-distances conjecture with a constant-factor bound.

- [The higher-dimensional Erdős distinct-distances conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/paper.pdf) -- no Lean statement
## 167. Planar distinct distances and unit-distance bounds

Proves the weak pinned Erdős distance conjecture: for every fixed ε &gt; 0, all but $`o(n)`$ points of any n-point planar set determine at least $`n^{1-\varepsilon}`$ distinct nonzero distances. A complementary theorem bounds the number of unit-distance pairs by $`O(n^{4/3-\delta})`$ for an absolute δ &gt; 0. ([Lean](lean/docs/167.md))

- [The weak pinned planar distance theorem](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-weak-pinned-planar-distance-theorem-September-23-2026/paper.pdf) -- formalized: `PinnedDistances`, `PlanarUnitDistances`
- [A power saving for planar unit distances](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-power-saving-for-planar-unit-distances-September-23-2026/paper.pdf) -- formalized: `PinnedDistances`, `PlanarUnitDistances`
## 168. Combinatorial invariance of Kazhdan–Lusztig polynomials

Resolves the full combinatorial invariance conjecture: isomorphic Bruhat intervals in arbitrary Coxeter systems have identical equal-parameter Kazhdan–Lusztig polynomials. Thus the abstract order of the interval determines the polynomial, even across different Coxeter systems. ([Lean](lean/docs/168.md))

- [Combinatorial invariance of Kazhdan–Lusztig polynomials](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf) -- formalized: `KLInvariance`
## 169. Shareshian–Wachs elementary positivity

Resolves the elementary-positivity part of the Shareshian–Wachs conjecture: the chromatic quasisymmetric function of every natural unit interval graph has elementary-basis coefficients in $`\mathbb N[q]`$. The coefficients count explicitly described permutations, giving a combinatorial explanation of positivity. ([Lean](lean/docs/169.md))

- [Elementary positivity of chromatic quasisymmetric functions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf) -- formalized: `ElementaryPositivity`
## 170. Sharp logarithmic exponents for off-diagonal Ramsey numbers

For every fixed integer s ≥ 5, proves $`r(s,t)=t^{s-1}/(\log t)^{s-2+o(1)}`$ as $`t\to\infty`$, determining the logarithmic exponent and matching the classical upper bound at that scale. Here $`r(s,t)`$ is the least number of vertices forcing an s-clique or a t-vertex independent set. ([Lean](lean/docs/170.md))

- [The sharp logarithmic exponent of r(5,t)](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Sharp-Logarithmic-Exponent-of-r-5-t-September-24-2026/paper.pdf) -- formalized: `RamseyFive`, `SharpLogRamsey`
- [Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf) -- formalized: `RamseyFive`, `SharpLogRamsey`
## 171. The hypercube Ramsey conjecture

Resolves the Burr–Erdős hypercube Ramsey conjecture: the two-color Ramsey number of the n-dimensional cube is $`\Theta(2^n)`$. Thus every red-blue coloring of a complete graph on a universal constant times the cube's number of vertices contains a monochromatic copy of the cube.

- [The hypercube Ramsey number has linear order](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-hypercube-Ramsey-number-has-linear-order-September-23-2026/paper.pdf) -- no Lean statement
## 172. Classification of finite Euclidean Ramsey configurations

Classifies finite point configurations that occur monochromatically, at their original scale, in every finite coloring of sufficiently high-dimensional Euclidean space. The characterization is an algebraic condition over the coordinate field. It also disproves the Leader–Russell–Walters conjecture that every such configuration is a subset of a finite transitive set. ([Lean](lean/docs/172.md))

- [A classification of finite Euclidean Ramsey configurations](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/paper.pdf) -- formalized: `EuclideanRamsey`, `GrahamSpherical`, `EuclideanRamseyCircle`, `EuclideanRamseyNine`, `EuclideanRamseyQuadratic`, `EuclideanRamseySpherical`, `EuclideanRamseyTransitive`
## 173. Seymour’s second-neighborhood conjecture

Proves Seymour's second-neighborhood conjecture: every nonempty finite oriented graph has a vertex with at least as many vertices at directed distance exactly two as at directed distance one. Oriented graphs may be arbitrary apart from the exclusion of loops and oppositely directed edge pairs. ([Lean](lean/docs/173.md))

- [A proof of Seymour’s second-neighborhood conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf) -- formalized: `SeymourSecondNeighborhood`
## 174. Deterministic construction of strong thin spanning trees

Resolves the strong thin-tree conjecture constructively. Every finite loopless k-edge-connected multigraph on at least two vertices has a spanning tree containing at most a universal $`C/k`$ fraction of the edges of every cut. Such a tree can be found deterministically in polynomial time, even with binary-encoded parallel-edge multiplicities. ([Lean](lean/docs/174.md))

- [The strong thin tree conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-strong-thin-tree-conjecture-September-23-2026/paper.pdf) -- formalized: `StrongThinTree`, `AlgorithmicThinTrees`
- [A polynomial-time construction of strong thin trees](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf) -- formalized: `StrongThinTree`, `AlgorithmicThinTrees`
## 175. Talagrand’s expectation thresholds, discrete convexity, and graph decompositions

Proves that integral and fractional expectation thresholds differ by at most a universal factor, and resolves Talagrand's discrete-convexity conjecture. An application proves the Ascoli–He–Park–Talagrand graph-decomposition conjecture: every graph's edges split into a universally bounded number of fixed pieces, each with containment threshold at most a universal constant times the original graph's integral expectation threshold. The pieces' embeddings need not agree on shared vertices. ([Lean](lean/docs/175.md))

- [Graph Decompositions at the Integral Expectation Threshold](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Graph-Decompositions-at-the-Integral-Expectation-Threshold-October-5-2026/graph-threshold-decompositions.pdf) -- no Lean statement
- [Integral and fractional expectation thresholds are equivalent](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Integral-and-fractional-expectation-thresholds-are-equivalent-September-23-2026/paper.pdf) -- formalized: `TalagrandExpectationThreshold`, `TalagrandDiscreteConvexity`
- [Talagrand’s discrete-convexity conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Talagrands-discrete-convexity-conjecture-September-23-2026/paper.pdf) -- formalized: `TalagrandExpectationThreshold`, `TalagrandDiscreteConvexity`
## 176. The second Kahn–Kalai conjecture with an edge-count bound

Proves the second Kahn–Kalai conjecture: for every finite simple graph H with h ≥ 1 edges and at most n vertices, its appearance threshold in $`G(n,p)`$ is at most $`C p_{\mathrm E}(n,H)(1+\log_2 h)`$, with universal C. Here $`p_{\mathrm E}`$ is the least density at which every subgraph of H has expected copy count at least 1/2. ([Lean](lean/docs/176.md))

- [The second Kahn–Kalai conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-second-Kahn-Kalai-conjecture-September-24-2026/paper.pdf) -- formalized: `SecondKahnKalai`
## 177. Bounded-degree coboundary expanders

Constructs arbitrarily large finite d-dimensional simplicial complexes, for every d ≥ 3, with uniformly bounded vertex degrees and uniform 𝔽2 coboundary expansion in every degree below d. Together with the known graph and two-dimensional cases, this establishes the existence of such expanders in every positive dimension. ([Lean](lean/docs/177.md))

- [Bounded-degree coboundary expanders in every dimension](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Bounded-degree-coboundary-expanders-in-every-dimension-September-24-2026/paper.pdf) -- formalized: `CoboundaryExpanders`
## 178. Deterministic nonbipartite Ramanujan graphs in every fixed degree

For every fixed d ≥ 3, constructs a simple d-regular nonbipartite Ramanujan graph on every sufficiently large even number n of vertices, with every nonconstant adjacency eigenvalue strictly between $`-2\sqrt{d-1}`$ and $`2\sqrt{d-1}`$. A deterministic algorithm outputs the full adjacency list in polynomial bit time, with exponent depending on d.

- [Deterministic nonbipartite Ramanujan graphs in every fixed degree](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Deterministic-nonbipartite-Ramanujan-graphs-in-every-fixed-degree-September-23-2026/paper.pdf) -- no Lean statement
## 179. The circulant Hadamard and Barker-sequence conjectures

Proves that real circulant Hadamard matrices exist exactly in orders 1 and 4, resolving the circulant Hadamard conjecture. Together with classical Barker-sequence results, this shows that binary sequences whose nontrivial aperiodic autocorrelations have magnitude at most 1 exist at lengths n &gt; 1 exactly when $`n\in\{2,3,4,5,7,11,13\}`$. ([Lean](lean/docs/179.md))

- [The circulant Hadamard conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-circulant-Hadamard-conjecture-September-23-2026/paper.pdf) -- formalized: `CirculantHadamard`, `EvenBarker`
## 180. Barnette’s Hamiltonian-cycle conjecture

Proves that every finite simple cubic bipartite planar 3-vertex-connected graph has a Hamiltonian cycle, resolving Barnette's conjecture. Equivalently, every three-edge path in a finite simple cubic 3-vertex-connected bipartite Pfaffian graph lies in a Hamiltonian cycle. ([Lean](lean/docs/180.md))

- [Paired states and Hamiltonian cycles in cubic bipartite planar graphs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/paper.pdf) -- formalized: `BarnetteHamiltonian`
## 181. The Erdős–Gallai cycle-decomposition conjecture

Proves that the edges of every finite simple undirected graph on n vertices can be partitioned into at most $`Cn`$ simple cycles and single edges, for an absolute constant C. This resolves the Erdős–Gallai cycle-decomposition conjecture, bounding the number of pieces linearly even for dense graphs. ([Lean](lean/docs/181.md))

- [A linear cycle-and-edge decomposition of every graph](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-linear-cycle-and-edge-decomposition-of-every-graph-September-24-2026/main.pdf) -- formalized: `CycleDecomposition`
## 182. Power savings for intersective polynomial differences and prime arguments

For every fixed intersective integer polynomial h of degree k ≥ 2 with positive leading coefficient, proves that a subset of $`\{1,\ldots,N\}`$ avoiding nonzero values $`h(1),h(2),\ldots`$ as differences has size $`O_h(N^{1-c_k})`$, with $`c_k\gt 0`$ depending only on degree. Here intersective means having a root modulo every modulus. For prime arguments, a power saving also holds when h has a unit root modulo every modulus, with exponent allowed to depend on h. ([Lean](lean/docs/182.md))

- [A power saving for intersective polynomial differences with an exponent depending only on the degree](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-power-saving-for-intersective-polynomial-differences-with-an-exponent-depending-only-on-the-degree-October-5-2026/power-saving-intersective-polynomial-differences.pdf) -- no Lean statement
- [A Power Saving for Polynomial Differences at Prime Arguments](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Power-Saving-for-Polynomial-Differences-at-Prime-Arguments-October-5-2026/prime-argument-polynomial-differences.pdf) -- no Lean statement
- [A power saving for square-difference-free sets](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-power-saving-for-square-difference-free-sets-September-24-2026/paper.pdf) -- formalized: `SquareDifference`
## 183. Power savings for planar halving lines and <i>k</i>-sets

Improves the planar halving-line bound to $`O(n^{4/3-\varepsilon})`$ for sets with no three collinear and an absolute ε &gt; 0. More generally, an n-point set with no three collinear has $`O(n(k+1)^{1/3-\varepsilon_0})`$ strictly separable k-subsets for $`1\le k\le n/2`$, with an absolute $`\varepsilon_0\gt 0`$. The constants and positive exponents are nonquantitative. ([Lean](lean/docs/183.md))

- [A power saving for planar halving lines](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-power-saving-for-planar-halving-lines-September-25-2026/main.pdf) -- formalized: `HalvingLines`
## 184. Correspondence coloring with a fixed forbidden subgraph

Proves the Alon–Krivelevich–Sudakov coloring conjecture in correspondence-coloring form: graphs avoiding any fixed subgraph F need $`O_F(\Delta/\log\Delta)`$ colors when their maximum degree Δ is sufficiently large. Also proves the Ajtai–Erdős–Komlós–Szemerédi independence conjecture: for fixed r ≥ 4, every n-vertex Kr-free graph of average degree d ≥ 2 has an independent set of size $`\Omega_r(n\log d/d)`$. ([Lean](lean/docs/184.md))

- [Correspondence coloring graphs with a forbidden clique](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Correspondence-Coloring-Graphs-with-a-Forbidden-Clique-October-5-2026/correspondence-coloring-forbidden-clique.pdf) -- no Lean statement
- [A logarithmic independence bound for clique-free graphs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Logarithmic-Independence-Bound-for-Clique-Free-Graphs-September-25-2026/paper.pdf) -- formalized: `CliqueFreeLog`
## 185. Counterexamples to infinite matroid intersection and packing/covering

Disproves the unrestricted infinite matroid intersection and packing/covering conjectures in ZFC, using two self-dual partitional matroids on a countably infinite ground set. The same examples answer Joó’s partitional-matroid question negatively. They are neither finitary nor cofinitary, so Nash-Williams’ original finitary conjecture remains outside the result. ([Lean](lean/docs/185.md))

- [A Counterexample to the Infinite Matroid Packing/Covering Conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Counterexample-to-the-Infinite-Matroid-Packing-Covering-Conjecture-September-24-2026/paper.pdf) -- formalized: `InfiniteMatroid`, `InfiniteMatroidCorollaries`
## 186. Uniform influence and sharp thresholds for graph and hypergraph properties

Proves the Friedgut–Kalai threshold-width conjectures for graphs and fixed-uniformity hypergraphs. For fixed $`0\lt \varepsilon\lt 1/2`$, every nontrivial increasing relabeling-invariant property crosses from probability ε to $`1-\varepsilon`$ within width $`O((\log n)^{-2})`$ for graphs and $`O_r((\log n)^{-r/(r-1)})`$ for r-uniform hypergraphs, r ≥ 3. The hypergraph influence bound also applies to nonmonotone properties. ([Lean](lean/docs/186.md))

- [A uniform influence bound for hypergraph properties](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-uniform-influence-bound-for-hypergraph-properties-October-5-2026/hypergraph-influences.pdf) -- no Lean statement
- [A Sharp Threshold Bound for Monotone Graph Properties](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Sharp-Threshold-Bound-for-Monotone-Graph-Properties-September-25-2026/paper.pdf) -- formalized: `SharpThreshold`
## 187. Snaky in 21 Maker moves

Settles the Snaky achievement problem: Maker can force the six-cell Snaky shape within 21 of its own moves on the initially empty infinite square board. Maker moves first, each player claims one free cell per turn, and translations, rotations and reflections count as wins. ([Lean](lean/docs/187.md))

- [Snaky in 21 Maker moves](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf) -- formalized: `SnakyCertificate`, `SnakyConditional`, `SnakyTwentyOne`
## 188. The sharp terminal leave in random triangle removal

Starting from the complete graph on n vertices, repeatedly delete a uniformly chosen remaining triangle. The terminal edge count is asymptotic to $`n^{3/2}/(2\sqrt2)`$, with mean-square convergence after normalization by n3/2. This proves the triangle case of the Joos–Kühn sharp-constant conjecture. ([Lean](lean/docs/188.md))

- [The sharp terminal leave in random triangle removal](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026.pdf) -- formalized: `TriangleRemoval`
## 189. Cycle–clique Ramsey numbers

Proves the Erdős–Faudree–Rousseau–Schelp conjecture: $`R(C_m,K_n)=(m-1)(n-1)+1`$ for every $`m\ge n\ge3`$, except $`R(C_3,K_3)=6`$. This is the exact threshold forcing a red m-cycle or a blue n-clique in every red–blue coloring of a complete graph. ([Lean](lean/docs/189.md))

- [Cycle--clique Ramsey numbers](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Cycle-clique-Ramsey-numbers-September-25-2026/Cycle-clique-Ramsey-numbers-September-25-2026.pdf) -- formalized: `CycleCliqueRamsey`
## 190. Polynomial removal fails for ordered binary matrices

Disproves polynomial ordered binary matrix removal with one fixed $`66\times66`$ zero–one pattern. Matrices can require many binary-entry changes to become pattern-free while their copy density is smaller than every proposed polynomial bound in that distance. Copies preserve row and column orders and match both zeros and ones. ([Lean](lean/docs/190.md))

- [Polynomial removal fails for ordered binary matrices](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Polynomial-removal-fails-for-ordered-binary-matrices-September-25-2026/paper.pdf) -- formalized: `MatrixRemoval`
## 191. A power improvement in the Heilbronn triangle lower bound

For every sufficiently large n, constructs n points in the unit square such that every triangle has area at least $`n^{-2+c}`$ for one absolute c &gt; 0. This disproves the conjectured almost-n−2 upper bound in Heilbronn's triangle problem, which asks how large the smallest determined triangle can be. ([Lean](lean/docs/191.md))

- [A power improvement in the Heilbronn triangle lower bound](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-power-improvement-in-the-Heilbronn-triangle-lower-bound-September-25-2026/main.pdf) -- formalized: `HeilbronnTriangle`
## 192. Boolean functions violate the square-root degree bound by arbitrary factors

Disproves the proposed square-root bound relating a Boolean function's linear Fourier coefficients to its polynomial degree. For every C &gt; 0, there is a sign-valued Boolean function f with $`\sum_i\widehat f(\{i\})\gt C\sqrt{\deg(f)}`$. Thus its total signed correlation with individual input bits can exceed the proposed bound by an arbitrary factor. ([Lean](lean/docs/192.md))

- [Unbounded Violations of the Square-Root Degree Bound](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Unbounded-Violations-of-the-Square-Root-Degree-Bound-September-26-2026/Unbounded-Violations-of-the-Square-Root-Degree-Bound-September-26-2026.pdf) -- formalized: `SquareRootDegree`
## 193. Serre’s intersection-multiplicity conjecture

Proves strict positivity of Serre's intersection multiplicity $`\chi^R(M,N)`$ for nonzero finitely generated modules over any regular local ring, provided $`M\otimes_R N`$ has finite length and $`\dim M+\dim N=\dim R`$. This resolves the positivity conjecture, including ramified mixed characteristic.

- [Positivity of Serre's Intersection Multiplicity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Positivity-of-Serres-Intersection-Multiplicity-September-23-2026/paper.pdf) -- no Lean statement
## 194. Lech’s multiplicity conjecture

Proves $`e(R)\le e(S)`$ for every flat local homomorphism of nonzero Noetherian local rings, where e is Hilbert–Samuel multiplicity. This resolves Lech's conjecture in every dimension and characteristic. ([Lean](lean/docs/194.md))

- [Lech's multiplicity conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf) -- formalized: `DuttaDomain`
## 195. A counterexample to the small Cohen–Macaulay module conjecture

Constructs a three-dimensional complete Noetherian normal local domain over ℂ with no nonzero finitely generated maximal Cohen–Macaulay module. A three-dimensional local domain essentially of finite type over ℂ has the same property, disproving the domain form of the small Cohen–Macaulay module conjecture. ([Lean](lean/docs/195.md))

- [A Complete Local Domain without a Small Cohen–Macaulay Module](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Complete-Local-Domain-Without-a-Small-Cohen-Macaulay-Module-September-23-2026/paper.pdf) -- formalized: `SurfaceConeCandidateSupport`
## 196. A counterexample to Kaplansky’s zero-divisor conjecture

Constructs a finitely presented torsion-free group G whose group algebra $`\mathbb F_2[G]`$ has nonzero zero divisors, disproving Kaplansky's zero-divisor conjecture. The group has a finite two-dimensional classifying space. ([Lean](lean/docs/196.md))

- [A Torsion-Free Group Algebra with Zero Divisors](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf) -- formalized: `TorsionFreeZeroDivisors`
## 197. A torsion-free group algebra that is not directly finite

Constructs a finitely presented torsion-free nonsofic group whose group algebra over 𝔽2 is not directly finite, disproving Kaplansky's conjecture even without torsion. Companion examples give injective nonsurjective cellular automata on all configurations, refuting Gottschalk's surjunctivity conjecture. Another counterexample is an integral group-ring matrix, invertible over the rational group ring, with Fuglede–Kadison determinant strictly between zero and one, disproving the unrestricted Determinant Conjecture. ([Lean](lean/docs/197.md))

- [A Torsion-Free Group Algebra That Is Not Directly Finite](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Torsion-Free-Group-Algebra-That-Is-Not-Directly-Finite-October-4-2026/direct-finiteness.pdf) -- no Lean statement
- [A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Characteristic Two](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026/paper.pdf) -- formalized: `KaplanskyFinitelyPresented`, `KaplanskyDirectFiniteness`, `GroupRingDeterminant`, `OddKaplansky`
- [A Counterexample to the Group-Ring Determinant Conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Counterexample-to-the-Group-Ring-Determinant-Conjecture-September-23-2026/paper.pdf) -- formalized: `KaplanskyFinitelyPresented`, `KaplanskyDirectFiniteness`, `GroupRingDeterminant`, `OddKaplansky`
- [A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Odd Characteristic](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Odd-Characteristic-September-26-2026/paper.pdf) -- formalized: `KaplanskyFinitelyPresented`, `KaplanskyDirectFiniteness`, `GroupRingDeterminant`, `OddKaplansky`
## 198. A counterexample to finitistic-dimension finiteness

Constructs a finite-dimensional complex algebra whose finite-dimensional modules have unbounded finite projective dimensions. This disproves the little finitistic-dimension conjecture. ([Lean](lean/docs/198.md))

- [An algebra of infinite little finitistic dimension](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf) -- formalized: `LittleFinitistic`, `FinitisticAsymmetry`
## 199. Counterexamples to Auslander–Reiten, Tachikawa and related homological conjectures

Constructs finite-dimensional algebras over a characteristic-two rational-function field that disprove the Auslander–Reiten and Gorenstein-projective conjectures, and Tachikawa's second conjecture. An associated endomorphism algebra also disproves the classical, generalized and strong Nakayama conjectures, the Auslander–Gorenstein conjecture, and the Wakamatsu tilting conjecture. The counterexamples persist under every extension of the base field. ([Lean](lean/docs/199.md))

- [An explicit counterexample to the Auslander-Reiten conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf) -- formalized: `AuslanderReiten`, `Tachikawa`
- [A counterexample to Tachikawa's second conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf) -- formalized: `AuslanderReiten`, `Tachikawa`
## 200. Eisenbud–Green–Harris and lex-plus-powers

Proves the Eisenbud–Green–Harris and lex-plus-powers conjectures over every characteristic-zero field. Any homogeneous ideal containing a regular sequence, of arbitrary length and degrees at least two, admits a lex-plus-powers ideal with the same Hilbert function and no smaller graded Betti numbers.

- [The Artinian Lex-Plus-Powers Betti Theorem](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Artinian-Lex-Plus-Powers-Betti-Theorem-September-23-2026/paper.pdf) -- no Lean statement
- [Commuting Division-Coefficient Forms and the Artinian Eisenbud--Green--Harris Conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Commuting-Division-Coefficient-Forms-and-the-Artinian-Eisenbud-Green-Harris-Conjecture-September-23-2026/paper.pdf) -- no Lean statement
## 201. A counterexample to Kurosh’s division-ring problem

Constructs a countable characteristic-zero division ring that is algebraic over its center and generated by two elements over that center, but has infinite dimension over it. This answers Kurosh's division-ring problem on local finiteness negatively.

- [A Counterexample to Kurosh’s Division-Ring Problem](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Counterexample-to-Kuroshs-Division-Ring-Problem-September-23-2026/paper.pdf) -- no Lean statement
## 202. The blockwise Alperin weight conjecture

Proves the numerical blockwise Alperin weight conjecture for every prime and every finite group: the number of irreducible Brauer characters in a block equals the number of conjugacy classes of its weights.

- [The Blockwise Alperin Weight Conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Blockwise-Alperin-Weight-Conjecture-September-23-2026/paper.pdf) -- no Lean statement
## 203. Donovan's conjecture over fields and complete mixed-characteristic DVRs

Proves Donovan's conjecture: over each fixed algebraically closed field of characteristic p, blocks of finite groups with bounded defect-group order have only finitely many Morita-equivalence classes, for every prime p. Also proves the integral form over each fixed complete mixed-characteristic discrete valuation ring with algebraically closed residue field.

- [Donovan's Conjecture over Algebraically Closed Fields](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Donovans-Conjecture-over-Algebraic-Closures-of-Prime-Fields-September-24-2026/main.pdf) -- no Lean statement
- [Integral Donovan Finiteness over Witt Vectors](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Integral-Donovan-Finiteness-over-Witt-Vectors-September-25-2026/main.pdf) -- no Lean statement
## 204. Tensor saturation for even spin groups

Proves saturation factor one for $`\mathop{\mathrm{Spin}}\nolimits (2n)`$, n ≥ 2: for three dominant integral weights whose sum lies in the root lattice, an invariant at any common positive integral dilation already gives an invariant at the original weights. This resolves the type-D part of the simply-laced saturation conjecture.

- [Tensor saturation for even spin groups](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Tensor-Saturation-for-Even-Spin-Groups-September-24-2026/Tensor-Saturation-for-Even-Spin-Groups-September-24-2026.pdf) -- no Lean statement
## 205. Saxl’s conjecture and universal tensor squares

Proves Saxl's conjecture: the tensor square of every staircase representation contains every irreducible complex representation of the corresponding symmetric group. More generally, every Sn with $`n\notin\{2,4,9\}`$ has an irreducible representation whose tensor square contains all irreducibles. ([Lean](lean/docs/205.md))

- [Universal Tensor Squares for Symmetric Groups](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf) -- formalized: `UniversalTensorSquares`, `Saxl`
- [A Cyclic Polytabloid Proof of Saxl's Conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Cyclic-Polytabloid-Proof-of-Saxls-Conjecture-September-24-2026/paper.pdf) -- formalized: `UniversalTensorSquares`, `Saxl`
## 206. Finite lattice representation and undecidability

Some finite lattices are not congruence lattices of any finite algebra, answering the finite lattice representation problem negatively. Moreover, no algorithm decides whether a finite lattice has such a representation, or whether it is a full subgroup interval of a finite group. ([Lean](lean/docs/206.md))

- [Finite congruence lattices: characterization and undecidability](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-Congruence-Lattices-Characterization-and-Undecidability-September-24-2026/paper.pdf) -- formalized: `FiniteCongruenceGraph`
- [A negative solution to the finite lattice representation problem](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Negative-Solution-to-the-Finite-Lattice-Representation-Problem-September-24-2026/paper.pdf) -- no Lean statement
## 207. The ℓ¹-Bass conjecture for all discrete groups

Proves the ℓ1-Bass conjecture for every discrete group: Hattori–Stallings traces of idempotent matrices over $`\ell^1(G)`$ are supported on finitely many finite-order conjugacy classes. The algebraic companion proves the integral Bass trace conjecture and Kaplansky's idempotent conjecture for torsion-free groups over every commutative unital characteristic-zero domain. ([Lean](lean/docs/207.md))

- [The ℓ¹-Bass Conjecture for Discrete Groups](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-l1-Bass-Conjecture-for-Discrete-Groups-October-5-2026/l1-bass-conjecture.pdf) -- no Lean statement
- [The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026.pdf) -- formalized: `BassTrace`, `BassTorsionFree`
## 208. Finite symmetric tensor categories and the Verlinde tower

Proves that every finite symmetric tensor category over an algebraically closed field k of characteristic p &gt; 0 admits a k-linear exact faithful strong symmetric monoidal fiber functor to a higher Verlinde category $`\mathrm{Ver}_{p^n}`$. The level may depend on the category, and the theorem includes characteristic two, resolving the finite case of the Benson–Etingof–Ostrik conjecture.

- [Fiber functors for finite symmetric tensor categories in positive characteristic](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Fiber-functors-for-finite-symmetric-tensor-categories-in-positive-characteristic-September-24-2026/paper.pdf) -- no Lean statement
## 209. Integral counterexamples to Gersten’s conjecture

Disproves unrestricted integral Gersten injectivity in degrees 3 and 5. Two explicit two-dimensional ramified regular local rings of mixed characteristic $`(0,5)`$ have nonzero integral K-theory classes that vanish over their fraction fields.

- [An integral counterexample to Gersten's conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-Integral-Counterexample-to-Gerstens-Conjecture-September-25-2026/An-Integral-Counterexample-to-Gerstens-Conjecture-September-25-2026.pdf) -- no Lean statement
- [An integral degree-three Gersten counterexample](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-Integral-Degree-Three-Gersten-Counterexample-September-26-2026/paper.pdf) -- no Lean statement
## 210. Foulkes' conjecture for sixth powers and quadratic stabilization

Proves the sixth case of Foulkes’ conjecture: $`\mathop{\mathrm{Sym}}\nolimits ^6(\mathop{\mathrm{Sym}}\nolimits ^bV)`$ embeds equivariantly in $`\mathop{\mathrm{Sym}}\nolimits ^b(\mathop{\mathrm{Sym}}\nolimits ^6V)`$ for every b ≥ 6 and finite-dimensional complex V. More generally, the canonical multiplication map $`\mathop{\mathrm{Sym}}\nolimits ^b(\mathop{\mathrm{Sym}}\nolimits ^aV)\to\mathop{\mathrm{Sym}}\nolimits ^a(\mathop{\mathrm{Sym}}\nolimits ^bV)`$ is surjective for a ≥ 2 and $`b\ge a(a-1)`$, giving dimension-independent quadratic stabilization. ([Lean](lean/docs/210.md))

- [Foulkes' conjecture for the sixth symmetric power](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Foulkes-Conjecture-for-the-Sixth-Symmetric-Power-September-25-2026/main.pdf) -- no Lean statement
- [Quadratic stabilization of the canonical Foulkes--Howe map](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quadratic-Stabilization-of-the-Canonical-Foulkes-Howe-Map-September-25-2026/paper.pdf) -- formalized: `FoulkesHowe`
## 211. The geometric phase diagram, diffusion, and spectra of random planar maps

Critical Fortuin–Kasteleyn planar maps converge to Liouville quantum gravity spheres for $`0\lt q\le4`$ and to the Brownian continuum random tree for q &gt; 4, establishing the surface-to-tree geometric transition. For FK–Ising and spanning-tree-weighted maps, stationary random walks converge to Liouville Brownian motion on the limiting sphere. The FK–Ising spectral result also gives convergence of eigenvalues and heat traces, using the stated Brownian/LQG inputs. ([Lean](lean/docs/211.md))

- [Random Walks on Critical FK–Ising Maps and Liouville Brownian Motion](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Random-Walks-on-Critical-FK-Ising-Maps-and-Liouville-Brownian-Motion-October-5-2026/fk-ising-walk-limit.pdf) -- no Lean statement
- [Spectral convergence for critical FK–Ising planar maps](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Spectral-convergence-for-critical-FK-Ising-planar-maps-October-5-2026/spectral-convergence-critical-fk-ising-planar-maps.pdf) -- no Lean statement
- [A Linear Clock for Random Walk on Tree-Weighted Planar Maps](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Linear-Clock-for-Random-Walk-on-Tree-Weighted-Planar-Maps-October-5-2026/linear-clock-random-walk-tree-weighted-planar-maps.pdf) -- no Lean statement
- [Canonical conformal limits of subcritical FK planar maps](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Canonical-conformal-limits-of-subcritical-FK-planar-maps-September-24-2026/main.pdf) -- no Lean statement
- [The critical Liouville quantum sphere and geometric limits of FK maps at q=4](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-critical-Liouville-quantum-sphere-and-geometric-limits-of-FK-maps-at-q-equals-4-September-24-2026/main.pdf) -- no Lean statement
- [Metric-measure limits of subcritical FK and spanning-tree planar maps](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Metric-measure-limits-of-subcritical-FK-and-spanning-tree-planar-maps-September-24-2026/main.pdf) -- no Lean statement
- [Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/main.pdf) -- formalized: `FKCRT`
## 212. Planar first-passage geometry and the absence of bigeodesics

Proves that planar first-passage percolation has no doubly infinite geodesic for iid nonnegative nonatomic edge weights when the minimum of four weights has finite second moment. For exponential weights, the limit shape is strictly convex with C1 boundary. Differentiability also holds for every Gamma law with positive shape and rate. ([Lean](lean/docs/212.md))

- [No bigeodesics in planar first-passage percolation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/No-bigeodesics-in-planar-first-passage-percolation-September-24-2026/main.pdf) -- no Lean statement
- [Strict convexity and differentiability of the planar exponential first-passage limit shape](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf) -- formalized: `PlanarFirstPassage`, `GammaPassage`
## 213. Critical percolation on every quasi-transitive graph

Resolves the Benjamini–Schramm criticality conjecture for bond percolation on every infinite connected locally finite quasi-transitive graph with $`p_c\lt 1`$: at the critical probability, there is almost surely no infinite cluster. The family also establishes this conclusion for both nearest-neighbor bond and site percolation on ℤ3. ([Lean](lean/docs/213.md))

- [Critical bond and site percolation on the cubic lattice](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Critical-bond-and-site-percolation-on-the-cubic-lattice-September-24-2026/paper.pdf) -- formalized: `CriticalZ3`, `CriticalPercolation`
- [No percolation at criticality on quasi-transitive graphs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf) -- formalized: `CriticalZ3`, `CriticalPercolation`
## 214. The Benjamini–Schramm nonuniqueness conjecture

Proves $`p_c\lt p_u`$ for Bernoulli bond percolation on every infinite connected locally finite nonamenable quasi-transitive graph, resolving the Benjamini–Schramm nonuniqueness conjecture. Thus there is a nonempty range of probabilities with infinitely many infinite clusters. A stronger operator bound also establishes the critical triangle condition. ([Lean](lean/docs/214.md))

- [Nonuniqueness of percolation on nonamenable quasi-transitive graphs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf) -- formalized: `BenjaminiSchramm`, `CayleyPercolation`
## 215. Canonical $`O(3)`$ continuum limit and exact $`O(4)`$ mass asymptotics

Constructs the canonical continuum limit of the two-dimensional nearest-neighbor $`O(3)`$ model: a non-Gaussian local relativistic theory with a unique vacuum and a positive mass gap. For the square-lattice $`O(4)`$ model, determines the exact leading asymptotic of the full transfer gap, $`m_{\mathrm{lat}}(\beta)\sim32e^{\pi/4-1/2}\sqrt\beta\,e^{-\pi\beta}`$. The family also proves exponential spin-correlation decay for two-dimensional nearest-neighbor $`O(n)`$ models with n ≥ 3 at every positive temperature. ([Lean](lean/docs/215.md))

- [The canonical massive continuum limit of the two-dimensional O(3) model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-canonical-massive-continuum-limit-of-the-two-dimensional-O3-model-October-4-2026/massive-continuum-o3.pdf) -- no Lean statement
- [An Isolated Particle Pole for the Two-Dimensional O(3) Spin Field](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-Isolated-Particle-Pole-for-the-Two-Dimensional-O3-Spin-Field-October-4-2026/o3-particle-pole.pdf) -- no Lean statement
- [Exact mass asymptotics for the two-dimensional O(4) lattice model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-mass-asymptotics-for-the-two-dimensional-O4-lattice-model-October-5-2026/exact-mass-o4.pdf) -- no Lean statement
- [Sharp mass bounds for the two-dimensional O(4) model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-mass-bounds-for-the-two-dimensional-O4-model-September-23-2026/paper.pdf) -- no Lean statement
- [Exponential decay in two-dimensional classical O(n) models](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exponential-decay-in-two-dimensional-classical-On-models-September-23-2026/paper.pdf) -- formalized: `ClassicalON`
## 216. Critical and near-critical XY scaling and BKT universality

For the square-lattice nearest-neighbor cosine XY model, proves critical axis correlations $`C_{\beta_c}(r)\sim Ar^{-1/4}(\log r)^{1/8}`$ and the Berezinskii–Kosterlitz–Thouless essential singularity $`\sqrt{\beta_c-\beta}\log\xi(\beta)\to B`$, with $`A,B\gt 0`$ after the free-box thermodynamic limit. For finite square-symmetric interactions containing nearest neighbors, discrete Gaussian heights converge to Gaussian fields throughout the rough phase, including its threshold, along geometric torus sizes. Critical center-magnetization and spin-field conclusions retain their stated height, renormalization, and field-input assumptions.

- [The critical logarithmic correction for the planar XY model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-critical-logarithmic-correction-for-the-planar-XY-model-October-5-2026/paper.pdf) -- no Lean statement
- [Critical Center Magnetization in the Planar XY Model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Critical-Center-Magnetization-in-the-Planar-XY-Model-October-5-2026/paper.pdf) -- no Lean statement
- [The Critical Spin Field of the Planar XY Model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Critical-Spin-Field-of-the-Planar-XY-Model-October-5-2026/paper.pdf) -- no Lean statement
- [Essential Singularity of the Correlation Length in the Planar XY Model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Essential-Singularity-of-the-Correlation-Length-in-the-Planar-XY-Model-October-5-2026/paper.pdf) -- no Lean statement
- [The critical correlation exponent of the planar XY model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-critical-correlation-exponent-of-the-planar-XY-model-September-24-2026/paper.pdf) -- no Lean statement
- [BKT universality for height and planar spin fields](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/BKT-universality-for-height-and-planar-spin-fields-September-24-2026/paper.pdf) -- no Lean statement
## 217. The low-temperature Sherrington–Kirkpatrick fluctuation law

For every fixed inverse temperature β &gt; 1, determines the fluctuation scale and limiting law of the zero-field Gaussian Sherrington–Kirkpatrick log partition function. Its variance is asymptotic to $`c_\beta n^{1/3}`$, with $`c_\beta\gt 0`$, confirming the predicted n1/6 standard-deviation scale. Exact centering and standardization give full-sequence convergence to a uniquely characterized nondegenerate law.

- [The low-temperature Sherrington–Kirkpatrick free-energy limiting law](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-low-temperature-Sherrington-Kirkpatrick-free-energy-limiting-law-September-24-2026/The-low-temperature-Sherrington-Kirkpatrick-free-energy-limiting-law-September-24-2026.pdf) -- no Lean statement
- [The low-temperature Sherrington–Kirkpatrick fluctuation scale](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-low-temperature-Sherrington-Kirkpatrick-fluctuation-scale-September-24-2026/The-low-temperature-Sherrington-Kirkpatrick-fluctuation-scale-September-24-2026.pdf) -- no Lean statement
## 218. Conformal universality for weakly interacting and random-bond Ising models

Weak finite-range square-symmetric even multispin perturbations of the square-lattice Ising model preserve critical bulk spin and energy limits; weak square-symmetric contour interactions also yield chordal SLE3 interface limits. With sufficiently weak iid bond disorder of any fixed bounded nondegenerate mean-zero law, critical spin interfaces converge to the same law in probability over environments. ([Lean](lean/docs/218.md))

- [Quenched SLE₃ limits for general weak random-bond Ising models](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quenched-SLE3-limits-for-general-weak-random-bond-Ising-models-October-5-2026/general-weak-random-bond-ising.pdf) -- no Lean statement
- [Quenched SLE₃ Universality for the Weak Random-Bond Ising Model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quenched-SLE3-Universality-for-the-Weak-Random-Bond-Ising-Model-October-5-2026/quenched-sle3-weak-random-bond-ising.pdf) -- no Lean statement
- [Logarithmic Relative Fluctuations in the Weakly Disordered Planar Ising Model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Logarithmic-Relative-Fluctuations-in-the-Weakly-Disordered-Planar-Ising-Model-October-5-2026/critical-relative-second-moment-weak-random-bond-ising.pdf) -- no Lean statement
- [Conformal universality of bulk Ising correlations under weak interactions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Conformal-universality-of-bulk-Ising-correlations-under-weak-interactions-September-23-2026/paper.pdf) -- no Lean statement
- [SLE3 universality for weak finite-range Ising interactions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/SLE3-universality-for-weak-finite-range-Ising-interactions-September-23-2026/paper.pdf) -- no Lean statement
- [Buffered comparison and stopping-band resolution in critical Ising](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Buffered-comparison-and-stopping-band-resolution-in-critical-Ising-September-23-2026/paper.pdf) -- formalized: `BufferedIsing`
## 219. GOE bulk universality for regular graphs with weak Anderson disorder

For every fixed degree d ≥ 3, the bulk adjacency-eigenvalue point process of a uniform simple random d-regular graph converges to the Gaussian orthogonal ensemble law, including for cubic graphs. The same fixed-energy universality persists under sufficiently weak fixed iid uniform diagonal disorder, throughout compact bands strictly inside the clean spectral edges.

- [Fixed-energy universality for weak Anderson disorder on random regular graphs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Fixed-energy-universality-for-weak-Anderson-disorder-on-random-regular-graphs-October-5-2026/fixed-energy-universality-weak-anderson-disorder-random-regular-graphs.pdf) -- no Lean statement
- [GOE bulk universality for fixed-degree random regular graphs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/GOE-bulk-universality-for-fixed-degree-random-regular-graphs-September-23-2026/paper.pdf) -- no Lean statement
## 220. Directional zero–one laws beyond iid environments and iid ballisticity

On ℤd, d ≥ 3, directional escape has probability zero or one for iid strictly elliptic nearest-neighbor environments, and for stationary ergodic finite-range-dependent environments under uniform ellipticity. In iid uniformly elliptic environments with d ≥ 2, almost-sure directional transience implies a deterministic limiting velocity with positive projection in that direction, resolving the ballisticity conjecture. ([Lean](lean/docs/220.md))

- [A directional zero–one law for finite-range-dependent random environments](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-directional-zero-one-law-for-finite-range-dependent-random-environments-October-5-2026/directional-zero-one-finite-range.pdf) -- no Lean statement
- [A directional zero–one law under strict ellipticity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-directional-zero-one-law-under-strict-ellipticity-September-23-2026/paper.pdf) -- formalized: `DirectionalWalk`, `DirectionalBallisticity`, `VelocityHemisphere`
- [Directional transience implies ballisticity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf) -- formalized: `DirectionalWalk`, `DirectionalBallisticity`, `VelocityHemisphere`
## 221. The Mézard–Parisi formula for diluted spin glasses

Proves the Mézard–Parisi hierarchical cavity formula for Poisson-diluted even-arity Ising models satisfying the Panchenko–Talagrand factorization and positivity assumptions, with only first-moment integrability. The limiting free energy equals the infimum over finite-depth hierarchical trial laws. This includes the Viana–Bray model, symmetric diluted even-spin models, and weighted soft even-K satisfiability. ([Lean](lean/docs/221.md))

- [The Mézard–Parisi formula for diluted spin glasses](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026/paper.pdf) -- formalized: `DilutedSpin`
## 222. Perceptron free energies and microscopic jamming exponents

Determines finite-temperature variational free energies for Gaussian Ising perceptrons with bounded Borel log-potentials and Gaussian spherical perceptrons with bounded continuous potentials, at every positive pattern density. A spherical extension treats bi-orthogonally invariant disorder with compact limiting singular-value distributions and no outliers. At margin −1, the quadratic-penalty spherical model has a sharp feasibility threshold and limiting gap and force laws, with system size, zero temperature, and critical density taken in that order. ([Lean](lean/docs/222.md))

- [The free energy of the Ising random perceptron](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-free-energy-of-the-Ising-random-perceptron-September-24-2026/The-free-energy-of-the-Ising-random-perceptron-September-24-2026.pdf) -- formalized: `IsingFiniteness`, `PerceptronFreeEnergy`, `SphericalField`
- [Microscopic jamming in the negative spherical perceptron](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Microscopic-jamming-in-the-negative-spherical-perceptron-September-24-2026/Microscopic-jamming-in-the-negative-spherical-perceptron-September-24-2026.pdf) -- no Lean statement
- [The spherical perceptron with bi-orthogonally invariant disorder](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-spherical-perceptron-with-bi-orthogonally-invariant-disorder-September-24-2026/The-spherical-perceptron-with-bi-orthogonally-invariant-disorder-September-24-2026.pdf) -- no Lean statement
- [The free energy of the spherical random perceptron](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-free-energy-of-the-spherical-random-perceptron-September-24-2026/The-free-energy-of-the-spherical-random-perceptron-September-24-2026.pdf) -- formalized: `IsingFiniteness`, `PerceptronFreeEnergy`, `SphericalField`
## 223. Random-cluster interfaces: critical, disordered, thermal, and natural-time scaling

Proves chordal SLEκ limits for critical square-lattice random-cluster interfaces for $`0\lt q\le4`$, with $`\kappa=4\pi/\arccos(-\sqrt q/2)`$: bounded Jordan domains are allowed for q ≥ 1, and smooth Jordan domains for q &lt; 1, under the stated marked-boundary approximations. For $`1\le q\le4`$, complete nested plane loops converge to CLEκ.

- [Square-lattice FK interfaces and nested loops for 1 <= q < 4](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Square-lattice-FK-interfaces-and-nested-loops-for-1-leq-q-lt-4-September-23-2026/paper.pdf) -- no Lean statement
- [Self-dual random-cluster interfaces below one](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Self-dual-random-cluster-interfaces-below-one-September-23-2026/paper.pdf) -- no Lean statement
- [Quenched SLE Universality for Weakly Disordered FK–Ising Interfaces](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quenched-SLE-Universality-for-Weakly-Disordered-FK-Ising-Interfaces-October-5-2026/quenched-fk-ising.pdf) -- no Lean statement
- [Thermal FK–Ising interfaces and massive SLE](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Thermal-FK-Ising-interfaces-and-massive-SLE-October-5-2026/paper.pdf) -- no Lean statement
- [Natural Occupation Measures for Critical Square-Lattice FK Interfaces](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Natural-Occupation-Measures-for-Critical-Square-Lattice-FK-Interfaces-October-5-2026/natural-occupation-measures-critical-square-lattice-fk-interfaces.pdf) -- no Lean statement
- [Conformal Limits of Critical Square-Lattice Random-Cluster Interfaces](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Conformal-Limits-of-Critical-Square-Lattice-Random-Cluster-Interfaces-October-5-2026/paper.pdf) -- no Lean statement
## 224. Critical and quenched near-critical universality for Poisson–Voronoi percolation

Proves Cardy's formula for annealed critical Poisson–Voronoi crossing probabilities in every bounded Jordan quadrilateral. With each model normalized by its own expected unit-square pivotal count, the conditional joint near-critical crossing-threshold laws for rational polygonal quads converge in environment probability to the triangular-lattice reference law. This establishes quenched near-critical universality for crossing thresholds.

- [From critical crossings to quenched near-critical universality in Voronoi percolation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/From-critical-crossings-to-quenched-near-critical-universality-in-Voronoi-percolation-October-5-2026/critical-crossings-quenched-near-critical-universality-voronoi-percolation.pdf) -- no Lean statement
- [A Pivotal Amplitude for Voronoi Percolation from Cardy's Formula](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Pivotal-Amplitude-for-Voronoi-Percolation-from-Cardys-Formula-October-5-2026/voronoi-pivotal-amplitude.pdf) -- no Lean statement
- [Cardy’s formula for critical Poisson–Voronoi percolation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Cardys-formula-for-critical-Poisson-Voronoi-percolation-September-23-2026/paper.pdf) -- no Lean statement
## 225. Gaussian free field limits throughout the balanced six-vertex regime

The balanced square-lattice six-vertex height field with $`a=b=1`$ and $`0\lt c\le2`$ converges to a Gaussian free field, including at the endpoint c = 2. The plane state is defined by balanced-torus limits. For unit height increments and Green kernel $`-(2\pi)^{-1}\log|x-y|`$, the exact variance multiplier is $`1/\arcsin(c/2)`$.

- [The Gaussian free field limit of the balanced six-vertex model with variance multiplier 1/arcsin(c/2)](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026.pdf) -- no Lean statement
## 226. The double-dimer loop ensemble converges to CLE<sub>4</sub>

Resolves the half-plane Temperleyan form of the double-dimer scaling-limit conjecture: the complete loop ensemble formed by two independent dimer coverings of the Temperleyan square lattice converges to nested CLE4. Convergence matches every macroscopic loop as an unparametrized curve, upgrading convergence of loop observables to convergence of the loops themselves.

- [The curve scaling limit of half-plane double dimers](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-curve-scaling-limit-of-half-plane-double-dimers-September-23-2026/paper.pdf) -- no Lean statement
## 227. Critical SK autocorrelation processes and dynamics across the temperature transition

For zero-field Gaussian SK heat-bath dynamics with rate-one updates per spin, proves worst-start cutoff on the $`\log n`$ scale for fixed $`0\le\beta\lt 1`$, mixing time $`n^{2/3+o(1)}`$ at β = 1, and stretched-exponential mixing from a Gibbs-sampled fixed starting configuration for β &gt; 1, in probability over disorder. At criticality, rescaled stationary and quench autocorrelation processes have universal random limits for Gaussian and Rademacher disorder; the quench limit relaxes to the stationary limit. ([Lean](lean/docs/227.md))

- [Universality of critical quench autocorrelations in the Sherrington–Kirkpatrick model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Universality-of-critical-quench-autocorrelations-in-the-Sherrington-Kirkpatrick-model-October-5-2026/main.pdf) -- no Lean statement
- [Functional universality of critical SK autocorrelations](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Functional-universality-of-critical-SK-autocorrelations-October-5-2026/critical-sk-autocorrelations.pdf) -- no Lean statement
- [A spectral gap throughout the high-temperature Sherrington–Kirkpatrick phase](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf) -- formalized: `SKHighTemperature`, `SKRatio`, `CriticalSKMixing`, `CriticalSK`, `SKBarriers`
- [Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf) -- formalized: `SKHighTemperature`, `SKRatio`, `CriticalSKMixing`, `CriticalSK`, `SKBarriers`
- [Critical slowing down in the Sherrington–Kirkpatrick model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf) -- formalized: `SKHighTemperature`, `SKRatio`, `CriticalSKMixing`, `CriticalSK`, `SKBarriers`
- [Stretched-exponential barriers for typical SK initial states](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf) -- formalized: `SKHighTemperature`, `SKRatio`, `CriticalSKMixing`, `CriticalSK`, `SKBarriers`
- [A typical-start upper bound for low-temperature SK Glauber dynamics](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-typical-start-upper-bound-for-low-temperature-SK-Glauber-dynamics-September-24-2026/paper.pdf) -- no Lean statement
- [Critical mixing in the Sherrington–Kirkpatrick model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Critical-mixing-in-the-Sherrington-Kirkpatrick-model-September-25-2026/paper.pdf) -- no Lean statement
## 228. Continuum phase transitions for radial pair potentials

Constructs stable distance-dependent pair interactions for three-dimensional classical particles with a first-order phase transition: the canonical free energy has a derivative jump at one inverse temperature throughout an open density interval. One potential has a divergent repulsive core; another is bounded and continuous with an integrable power-law tail, realizing the type of transition sought in Simon's continuum problem. ([Lean](lean/docs/228.md))

- [A continuum temperature singularity for a radial pair potential](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-continuum-temperature-singularity-for-a-radial-pair-potential-September-24-2026/paper.pdf) -- formalized: `ContinuumTransition`, `RadialTransition`, `RadialDensityInterval`
- [A radial continuum phase transition with algebraic decay](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf) -- formalized: `ContinuumTransition`, `RadialTransition`, `RadialDensityInterval`
## 229. Exact three- and four-state reconstruction thresholds and four-state tree capacity

Proves the exact reconstruction threshold $`d\lambda^2\gt 1`$, with nonreconstruction at equality, for three-state symmetric and four-state ferromagnetic broadcasting on regular trees (d ≥ 2) and observed Poisson trees (mean d &gt; 1 and d &gt; 0, respectively), with Poisson advantage averaged without conditioning on survival. The three-state theorem allows both signs of λ and gives the exact weak-recovery threshold for the symmetric three-community stochastic block model. ([Lean](lean/docs/229.md))

- [The Reconstruction Threshold for the Ferromagnetic Four-State Potts Model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Reconstruction-Threshold-for-the-Ferromagnetic-Four-State-Potts-Model-October-5-2026/four-state-potts.pdf) -- no Lean statement
- [A Capacity Criterion for Four-State Potts Reconstruction on Trees](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Capacity-Criterion-for-Four-State-Potts-Reconstruction-on-Trees-October-5-2026/four-state-capacity.pdf) -- no Lean statement
- [The exact reconstruction threshold for the three-state symmetric channel](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-exact-reconstruction-threshold-for-the-three-state-symmetric-channel-September-25-2026/paper.pdf) -- formalized: `ThreeStateSupercritical`, `ThreeStateTreeClauses`
## 230. Exact Hausdorff gauges for SLE

Resolves Schramm’s Hausdorff-measure question for chordal SLEκ, $`0\lt \kappa\lt 8`$. The explicit gauge $`r^d(\log\log(1/r))^{(2-d)/2}`$, $`d=1+\kappa/8`$, gives almost surely positive finite measure to every trace segment $`\gamma([s,t])`$ with $`0\lt s\lt t\lt \infty`$, and finite expected measure to the trace in every bounded disk. ([Lean](lean/docs/230.md))

- [An exact Hausdorff gauge for SLE](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-exact-Hausdorff-gauge-for-SLE-September-25-2026/An-exact-Hausdorff-gauge-for-SLE-September-25-2026.pdf) -- formalized: `SLELowerPositivity`
- [An explicit exact Hausdorff gauge for SLE](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-exact-Hausdorff-gauge-for-SLE-September-26-2026/An-explicit-exact-Hausdorff-gauge-for-SLE-September-26-2026.pdf) -- formalized: `SLELowerPositivity`
## 231. The free uniform spanning forest is a factor of IID

On every infinite connected locally finite simple unweighted graph, the free uniform spanning forest is a factor of independent vertex labels, by one isomorphism-equivariant rule using no root. Translation-invariant strongly Rayleigh binary processes on every countable group, including invariant determinantal processes with Hermitian positive-contraction kernels, are also factors of IID. ([Lean](lean/docs/231.md))

- [The free uniform spanning forest is a factor of IID](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026.pdf) -- formalized: `StronglyRayleighDPP`, `FreeUniformSpanningForest`
## 232. Gaussian fields and interfaces for triangular-lattice Lipschitz heights

Proves Gaussian free field limits on bounded smooth simply connected domains for triangular-lattice height models: uniform odd heights with increments $`0,\pm2`$ and two-arc boundary values $`\pm1`$, and zero-boundary integer Lipschitz heights weighted by fixed $`x\in[1/\sqrt2,1]`$. Uniform real Lipschitz heights also converge to a Gaussian field; at a tuned opposite-boundary amplitude, their interface converges to chordal SLE4, establishing Schramm’s real-field/interface predictions.

- [Gaussian free-field limits of weighted integer Lipschitz heights](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Gaussian-free-field-limits-of-weighted-integer-Lipschitz-heights-October-6-2026/paper.pdf) -- no Lean statement
- [The Gaussian free field limit of integer Lipschitz heights with two-arc boundary data](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Gaussian-free-field-limit-of-integer-Lipschitz-heights-with-two-arc-boundary-data-October-6-2026/paper.pdf) -- no Lean statement
- [Uniform real Lipschitz surfaces on the triangular lattice](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-real-Lipschitz-surfaces-on-the-triangular-lattice-October-6-2026/paper.pdf) -- no Lean statement
## 233. The joint critical Ashkin–Teller current limit

Identifies the joint scaling limit of Ashkin–Teller heights and both complete current-cluster collections throughout the critical line, including the four-state Potts endpoint. In bounded Jordan domains with admissible lattice approximations and wired primal/free dual boundaries, the height converges to the predicted Gaussian free field, and the clusters to canonical recursive sets of that same field, retaining every nesting depth.

- [The joint scaling limit of critical Ashkin-Teller currents](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-joint-scaling-limit-of-critical-Ashkin-Teller-currents-October-6-2026/main.pdf) -- no Lean statement
## 234. All-temperature pressure of orthogonally invariant Ising spin glasses

Gives an exact variational formula for the limiting pressure of orthogonally invariant Ising spin glasses at every fixed temperature, both almost surely and in expectation. The coupling matrix is a Haar-random rotation of a deterministic spectrum converging to a compactly supported law, with extreme eigenvalues converging to its support edges. The zero-field ground-state energy follows as temperature tends to zero. ([Lean](lean/docs/234.md))

- [All-temperature pressure for orthogonally invariant Ising spin glasses](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf) -- formalized: `InvariantIsing`
## 235. Limiting random SAT thresholds, sharp variance and computability

For random k-SAT with independent uniformly signed proper clauses sampled with replacement, proves finite positive limiting thresholds and hitting-time variance $`\Theta_k(n)`$ for every fixed k ≥ 3, and computability of the 3-SAT threshold. We credit Gaia Carenini with priority for resolving the threshold-existence conjecture in her concurrent [ECCC TR26-229](https://eccc.weizmann.ac.il/report/2026/229/), made public October 5, 2026; this family supplies another proof and the sharper variance and computability results. ([Lean](lean/docs/235.md))

- [A Limiting Satisfiability Threshold for Every Fixed Clause Size](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Limiting-Satisfiability-Threshold-for-Every-Fixed-Clause-Size-September-25-2026/article.pdf) -- formalized: `FixedClauseThreshold`, `SATSharpness`, `SATVariance`, `SATComputability`
- [Linear Variance of the Random 3-SAT Hitting Time](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Linear-Variance-of-the-Random-3-SAT-Hitting-Time-October-5-2026/linear-variance-of-the-random-3-sat-hitting-time.pdf) -- no Lean statement
- [Variance of the Random k-SAT Hitting Time](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Variance-of-the-Random-k-SAT-Hitting-Time-September-27-2026/article.pdf) -- formalized: `FixedClauseThreshold`, `SATSharpness`, `SATVariance`, `SATComputability`
- [Computing the Random 3-SAT Threshold](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf) -- formalized: `FixedClauseThreshold`, `SATSharpness`, `SATVariance`, `SATComputability`
## 236. The exact factor-of-IID threshold for free Ising spins on trees

Determines when the free zero-field ferromagnetic Ising state on the infinite d-regular tree is a factor of independent vertex labels: exactly when $`\tanh\beta\le(d-1)^{-1/2}`$, including equality, for d ≥ 3 and β ≥ 0. The construction uses no root and is almost surely equivariant for each fixed tree automorphism, resolving the ferromagnetic case of Lyons's question. ([Lean](lean/docs/236.md))

- [The sharp factor-of-IID threshold for the free Ising model on regular trees](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf) -- formalized: `FreeIsing`
## 237. The three-quarter exponent for honeycomb self-avoiding walk

Proves the diameter form of Nienhuis's predicted three-quarter exponent: a uniformly chosen n-step self-avoiding walk on the honeycomb lattice has diameter $`n^{3/4+o(1)}`$. Its local mass and covering numbers have exponent 4/3. These estimates hold at every sufficiently large fixed length, simultaneously across scales, with arbitrarily high polynomial probability. ([Lean](lean/docs/237.md))

- [Radial transfer estimates and polygon length laws for honeycomb walks](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Radial-transfer-estimates-and-polygon-length-laws-for-honeycomb-walks-September-26-2026/main.pdf) -- no Lean statement
- [Critical honeycomb chords with prescribed boundary endpoints](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Critical-honeycomb-chords-with-prescribed-boundary-endpoints-September-26-2026/main.pdf) -- formalized: `HoneycombBridgeFiniteness`, `HoneycombFreeEnergy`, `CriticalStripMass`, `HoneycombBridgeMassSupport`
- [Cylinder loop weights and planar nesting](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Cylinder-loop-weights-and-planar-nesting-September-26-2026/main.pdf) -- no Lean statement
- [Mass and covering exponents for fixed-length honeycomb walks](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Mass-and-covering-exponents-for-fixed-length-honeycomb-walks-September-26-2026/main.pdf) -- no Lean statement
- [Signed cylinder propagation and marked polygons on the honeycomb lattice](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Signed-cylinder-propagation-and-marked-polygons-on-the-honeycomb-lattice-September-26-2026/main.pdf) -- no Lean statement
- [Cylinder amplitudes and logarithmic bridge-length windows on the honeycomb lattice](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Cylinder-amplitudes-and-logarithmic-bridge-length-windows-on-the-honeycomb-lattice-September-26-2026/main.pdf) -- no Lean statement
- [Marked polygon correlations and one-arc bounds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Marked-polygon-correlations-and-one-arc-bounds-September-26-2026/main.pdf) -- no Lean statement
- [Disk transfer representations and confined bridge mass](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Disk-transfer-representations-and-confined-bridge-mass-September-26-2026/main.pdf) -- no Lean statement
- [Polynomial vacuum representations and bridge mass for honeycomb walks](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Polynomial-vacuum-representations-and-bridge-mass-for-honeycomb-walks-September-26-2026/main.pdf) -- formalized: `HoneycombBridgeFiniteness`, `HoneycombFreeEnergy`, `CriticalStripMass`, `HoneycombBridgeMassSupport`
- [Renewal and changes of law for critical honeycomb walks](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Renewal-and-changes-of-law-for-critical-honeycomb-walks-September-26-2026/main.pdf) -- formalized: `HoneycombBridgeFiniteness`, `HoneycombFreeEnergy`, `CriticalStripMass`, `HoneycombBridgeMassSupport`
- [Critical strip-crossing mass on the honeycomb lattice](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf) -- formalized: `HoneycombBridgeFiniteness`, `HoneycombFreeEnergy`, `CriticalStripMass`, `HoneycombBridgeMassSupport`
- [Uniform marked-polygon estimates and sharp finite bridge moments](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-marked-polygon-estimates-and-sharp-finite-bridge-moments-September-26-2026/main.pdf) -- no Lean statement
- [Cap-selected amplitudes and triangle chords for honeycomb walks](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Cap-selected-amplitudes-and-triangle-chords-for-honeycomb-walks-September-26-2026/main.pdf) -- no Lean statement
## 238. Optimal logarithmic mixing of the Thorp shuffle

Proves that the Thorp shuffle randomizes $`N=2^d`$ labeled cards in $`\Theta(\log N)`$ physical shuffles, settling its optimal mixing order for power-of-two deck sizes. Convergence is in total variation from the worst initial ordering and concerns the entire permutation, not just individual card positions. ([Lean](lean/docs/238.md))

- [Optimal-order mixing of the Thorp shuffle](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Optimal-order-mixing-of-the-Thorp-shuffle-September-26-2026/paper.pdf) -- formalized: `ThorpFirstReciprocal`, `ThorpRemaining`, `PartialPermutation`, `ThorpRouting`, `OccupiedOverlap`, `WeightedSweepMoments`, `CoordinateTrace`, `ThorpWeightedCompatibility`, `SpinAngle`, `SignedSweepMoment`, `BinarySweep`, `CoordinateSweeps`, `FourRowPermanent`
- [Random coordinate frames and partial permutation laws](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Random-coordinate-frames-and-partial-permutation-laws-September-26-2026/main.pdf) -- no Lean statement
- [From partial permutation information to Fourier bounds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/From-partial-permutation-information-to-Fourier-bounds-September-26-2026/main.pdf) -- formalized: `ThorpFirstReciprocal`, `ThorpRemaining`, `PartialPermutation`, `ThorpRouting`, `OccupiedOverlap`, `WeightedSweepMoments`, `CoordinateTrace`, `ThorpWeightedCompatibility`, `SpinAngle`, `SignedSweepMoment`, `BinarySweep`, `CoordinateSweeps`, `FourRowPermanent`
- [Conditional information under deterministic coordinate sweeps](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Conditional-information-under-deterministic-coordinate-sweeps-September-26-2026/main.pdf) -- no Lean statement
- [Conditional permutations in a revealed switching environment](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Conditional-permutations-in-a-revealed-switching-environment-September-26-2026/paper.pdf) -- formalized: `ThorpFirstReciprocal`, `ThorpRemaining`, `PartialPermutation`, `ThorpRouting`, `OccupiedOverlap`, `WeightedSweepMoments`, `CoordinateTrace`, `ThorpWeightedCompatibility`, `SpinAngle`, `SignedSweepMoment`, `BinarySweep`, `CoordinateSweeps`, `FourRowPermanent`
- [Routing densities and representation contraction for Thorp sweeps](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Routing-densities-and-representation-contraction-for-Thorp-sweeps-September-26-2026/paper.pdf) -- formalized: `ThorpFirstReciprocal`, `ThorpRemaining`, `PartialPermutation`, `ThorpRouting`, `OccupiedOverlap`, `WeightedSweepMoments`, `CoordinateTrace`, `ThorpWeightedCompatibility`, `SpinAngle`, `SignedSweepMoment`, `BinarySweep`, `CoordinateSweeps`, `FourRowPermanent`
- [Row&#8211;column symmetry and contraction of coordinate sweeps](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf) -- formalized: `ThorpFirstReciprocal`, `ThorpRemaining`, `PartialPermutation`, `ThorpRouting`, `OccupiedOverlap`, `WeightedSweepMoments`, `CoordinateTrace`, `ThorpWeightedCompatibility`, `SpinAngle`, `SignedSweepMoment`, `BinarySweep`, `CoordinateSweeps`, `FourRowPermanent`
- [Random-subspace tests and trace smoothing for coordinate sweeps](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Random-subspace-tests-and-trace-smoothing-for-coordinate-sweeps-September-26-2026/paper.pdf) -- formalized: `ThorpFirstReciprocal`, `ThorpRemaining`, `PartialPermutation`, `ThorpRouting`, `OccupiedOverlap`, `WeightedSweepMoments`, `CoordinateTrace`, `ThorpWeightedCompatibility`, `SpinAngle`, `SignedSweepMoment`, `BinarySweep`, `CoordinateSweeps`, `FourRowPermanent`
- [Compatibility entropy and the spectrum of a Thorp sweep](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Compatibility-entropy-and-the-spectrum-of-a-Thorp-sweep-September-26-2026/paper.pdf) -- formalized: `ThorpFirstReciprocal`, `ThorpRemaining`, `PartialPermutation`, `ThorpRouting`, `OccupiedOverlap`, `WeightedSweepMoments`, `CoordinateTrace`, `ThorpWeightedCompatibility`, `SpinAngle`, `SignedSweepMoment`, `BinarySweep`, `CoordinateSweeps`, `FourRowPermanent`
- [Signed tensor densities and diagram budgets for the Thorp shuffle](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf) -- formalized: `ThorpFirstReciprocal`, `ThorpRemaining`, `PartialPermutation`, `ThorpRouting`, `OccupiedOverlap`, `WeightedSweepMoments`, `CoordinateTrace`, `ThorpWeightedCompatibility`, `SpinAngle`, `SignedSweepMoment`, `BinarySweep`, `CoordinateSweeps`, `FourRowPermanent`
- [Conditional coordinate sweeps and analytic transfer](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Conditional-coordinate-sweeps-and-analytic-transfer-September-26-2026/main.pdf) -- formalized: `ThorpFirstReciprocal`, `ThorpRemaining`, `PartialPermutation`, `ThorpRouting`, `OccupiedOverlap`, `WeightedSweepMoments`, `CoordinateTrace`, `ThorpWeightedCompatibility`, `SpinAngle`, `SignedSweepMoment`, `BinarySweep`, `CoordinateSweeps`, `FourRowPermanent`
- [A strict four-row permanent inequality and permutation moments](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026/main.pdf) -- formalized: `ThorpFirstReciprocal`, `ThorpRemaining`, `PartialPermutation`, `ThorpRouting`, `OccupiedOverlap`, `WeightedSweepMoments`, `CoordinateTrace`, `ThorpWeightedCompatibility`, `SpinAngle`, `SignedSweepMoment`, `BinarySweep`, `CoordinateSweeps`, `FourRowPermanent`
## 239. Sharp singularity rates for symmetric random sign matrices

Determines the sharp exponential singularity rate of symmetric random sign matrices with independent entries on and above the diagonal. Uniform signs give $`\Pr(\det A_n=0)=(1/2+o(1))^n`$; for fixed bias $`p\in(0,1)\setminus\{1/2\}`$, the rate is $`(p^2+(1-p)^2+o(1))^n`$. In the biased case, agreeing rows attain this rate.

- [The sharp exponential rate of singularity for symmetric Bernoulli matrices](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-sharp-exponential-rate-of-singularity-for-symmetric-Bernoulli-matrices-October-3-2026/symmetric-bernoulli-singularity.pdf) -- no Lean statement
- [The sharp singularity rate for biased symmetric sign matrices](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-sharp-singularity-rate-for-biased-symmetric-sign-matrices-October-4-2026/biased-symmetric-sign-singularity.pdf) -- no Lean statement
## 240. Shelah's eventual categoricity and the prescribed-threshold obstruction

Proves Shelah's eventual categoricity conjecture in ZFC: for each bound on the Löwenheim–Skolem number, a uniform threshold makes categoricity of an abstract elementary class in one cardinal above that threshold imply categoricity throughout the same tail. Categoricity means uniqueness up to isomorphism at a given cardinality. Under the continuum hypothesis, a proposed specific Hanf threshold need not suffice. ([Lean](lean/docs/240.md))

- [A CH obstruction to a prescribed categoricity threshold](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-CH-Obstruction-to-a-Prescribed-Categoricity-Threshold-September-24-2026/paper.pdf) -- formalized: `CHObstruction`
- [Eventual categoricity for abstract elementary classes](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Eventual-Categoricity-for-Abstract-Elementary-Classes-September-24-2026/paper.pdf) -- no Lean statement
## 241. Rigidity of the Turing degrees

Every order automorphism of the Turing degrees is the identity, resolving their rigidity problem. Thus no nontrivial relabeling of degrees preserves the ordering by relative computability. ([Lean](lean/docs/241.md))

- [Rigidity of the Turing degrees](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf) -- formalized: `DegreeRigidity`
## 242. Single-fold Diophantine representations and undecidability under an at-most-one-solution promise

Every recursively enumerable set of tuples of natural numbers has a Diophantine representation with exactly one auxiliary solution for each member and none for nonmembers. This proves the single-fold conjecture and hence the finite-fold conjecture. Diophantine solvability over the nonnegative integers remains undecidable even with an at-most-one-solution promise. ([Lean](lean/docs/242.md))

- [Single-fold Diophantine representations](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Single-fold-Diophantine-representations-September-24-2026/paper.pdf) -- formalized: `SingleFold`
## 243. Separating choiceless counting from polynomial time and witnessed choice

Confirms the Blass–Gurevich–Shelah noncapture conjecture: consistency of a linear system over 𝔽3 defines a polynomial-time query on unordered finite structures that choiceless polynomial time with counting cannot express. A separate result shows that adding witnessed symmetric choice strictly increases expressive power. Both separations hold for the full counting formalism, allowing hereditarily finite sets of arbitrary finite rank. ([Lean](lean/docs/243.md))

- [Choiceless polynomial time with counting does not capture polynomial time](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Choiceless-polynomial-time-with-counting-does-not-capture-polynomial-time-September-23-2026/paper.pdf) -- formalized: `ChoicelessPolynomialTime`, `WitnessedChoice`
- [Witnessed symmetric choice is strictly stronger than choiceless polynomial time with counting](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Witnessed-symmetric-choice-is-strictly-stronger-than-choiceless-polynomial-time-with-counting-September-24-2026/paper.pdf) -- formalized: `ChoicelessPolynomialTime`, `WitnessedChoice`
## 244. The Partition Principle does not imply Choice

Assuming ZF is consistent, constructs a model in which every surjective image of a set injects into that set, yet the axiom of choice fails. Choice for ordinal-indexed families still holds. From any countable transitive model of ZFC, a separate construction gives a transitive symmetric extension with these properties and no new countable sequences of ground-model elements. ([Lean](lean/docs/244.md))

- [The Partition Principle does not imply Choice](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf) -- formalized: `PartitionPrinciple`, `PartitionConsistency`
## 245. Weak normalization implies strong normalization in pure type systems

Proves that weak normalization implies strong normalization for every pure type system: if every legal expression in every valid context has a β-normal form, every β-reduction sequence terminates. This resolves the β-Barendregt–Geuvers–Klop conjecture, including nonfunctional rules and open contexts. ([Lean](lean/docs/245.md))

- [Weak and strong normalization in pure type systems](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Weak-and-strong-normalization-in-pure-type-systems-September-25-2026/paper.pdf) -- formalized: `TypeSystemNormalization`
## 246. Cannon's conjecture

Every word-hyperbolic group with boundary homeomorphic to S2 admits a proper cocompact isometric action on hyperbolic three-space with finite kernel, proving Cannon's conjecture. Every torsion-free such group is therefore the fundamental group of a closed hyperbolic three-manifold. ([Lean](lean/docs/246.md))

- [A Modulus Proof of Cannon’s Conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Modulus-Proof-of-Cannons-Conjecture-September-23-2026/paper.pdf) -- formalized: `CannonGeometricAction`
## 247. An infinite finitely presented residually finite 2-group and a finitely presented nil algebra

Constructs an infinite finitely presented residually finite group whose elements all have finite 2-power order, answering the finitely presented Burnside problem negatively even in this class. The construction also yields an infinite-dimensional finitely presented nil associative 𝔽2-algebra and a finitely presented infinite-dimensional algebraic unitization, giving negative answers to the corresponding nilpotence and Kurosh finiteness questions. ([Lean](lean/docs/247.md))

- [An infinite finitely presented residually finite 2-group](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-infinite-finitely-presented-residually-finite-2-group-October-5-2026/residually-finite-torsion.pdf) -- no Lean statement
- [An infinite finitely presented periodic group](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf) -- formalized: `PeriodicGroup`
## 248. Thompson's group <i>F</i> is nonamenable

Proves that Thompson's group F, the group of dyadic piecewise linear homeomorphisms of the interval, is nonamenable, resolving its longstanding amenability problem. ([Lean](lean/docs/248.md))

- [Thompson's group F is nonamenable](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Thompsons-group-F-is-nonamenable-September-23-2026/paper.pdf) -- formalized: `ThompsonNonamenability`
## 249. A finitely generated Eilenberg–Ganea counterexample

Constructs a finitely generated residually finite group with integral cohomological dimension two and geometric dimension three, disproving the Eilenberg–Ganea conjecture. It has no two-dimensional classifying space, even with infinitely many cells. ([Lean](lean/docs/249.md))

- [A finitely generated counterexample to the Eilenberg–Ganea conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf) -- formalized: `EilenbergGanea`
## 250. Boone–Higman embeddings with higher finiteness

A finitely generated group has decidable word problem exactly when it embeds in a finitely presented simple group, proving the Boone–Higman conjecture. The target can have type F∞: a classifying space with finitely many cells in each dimension. A single group of type F∞ can also contain every finitely presented group. ([Lean](lean/docs/250.md))

- [Finite algebraic envelopes and the Boone–Higman conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf) -- formalized: `BooneHigman`, `SimpleOvergroups`, `UniversalFInfinity`
- [Simple F∞ overgroups of groups with decidable word problem](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Simple-F-infinity-overgroups-of-groups-with-decidable-word-problem-September-23-2026/paper.pdf) -- formalized: `BooneHigman`, `SimpleOvergroups`, `UniversalFInfinity`
- [A universal group of type F∞](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf) -- formalized: `BooneHigman`, `SimpleOvergroups`, `UniversalFInfinity`
## 251. Amenability, unitarizability, and strong Ulam stability

Resolves Dixmier's problem for all discrete groups: amenability is equivalent to every uniformly bounded Hilbert-space representation being similar to a unitary representation. For countable discrete groups, amenability is also equivalent to strong Ulam stability: sufficiently accurate unitary approximate representations are uniformly close in operator norm to genuine representations on the same, possibly infinite-dimensional, Hilbert space. ([Lean](lean/docs/251.md))

- [Unitarizability implies amenability for discrete groups](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Unitarizability-Implies-Amenability-for-Countable-Groups-September-23-2026/paper.pdf) -- formalized: `DixmierAllDiscrete`, `Dixmier`
- [Strong Ulam Stability Characterizes Amenability](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Strong-Ulam-Stability-Characterizes-Amenability-October-5-2026/strong-ulam-stability.pdf) -- no Lean statement
## 252. A torsion-free hyperbolic group that is neither residually finite nor linear over any field

Constructs a torsion-free word-hyperbolic group that is not residually finite, answering the residual-finiteness question negatively. One fixed nonidentity element is killed by every finite-dimensional linear representation over every commutative field, so the group is not linear over any such field. ([Lean](lean/docs/252.md))

- [A torsion-free hyperbolic group that is not residually finite](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/a-torsion-free-hyperbolic-group-that-is-not-residually-finite-September-23-2026/paper.pdf) -- formalized: `TorsionFreeHyperbolic`
## 253. An infinite finitely presented simple amenable group

Constructs an infinite finitely presented simple amenable group, answering the longstanding question of whether these properties can occur simultaneously. ([Lean](lean/docs/253.md))

- [An infinite finitely presented simple amenable group](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf) -- formalized: `SimpleAmenable`
## 254. Classifying spaces and geometric obstructions for Artin groups

The Salvetti complex of every finite-rank Artin group is aspherical, proving the Artin $`K(\pi,1)`$ conjecture. Arbitrary intersections of its parabolic subgroups are parabolic, proving the Parabolic Intersection Conjecture. An explicit Artin group admits no proper cocompact isometric action on any nonempty proper CAT$`(0)`$ space. ([Lean](lean/docs/254.md))

- [Harmonic heights and the Artin K(pi,1) conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf) -- formalized: `HarmonicArtin`, `ArtinCAT0`, `ArtinParabolicIntersections`
- [An Artin group with no geometric CAT(0) action](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-Artin-group-with-no-geometric-CAT-0-action-September-23-2026/paper.pdf) -- formalized: `HarmonicArtin`, `ArtinCAT0`, `ArtinParabolicIntersections`
- [Parabolic intersections in Artin groups](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf) -- formalized: `HarmonicArtin`, `ArtinCAT0`, `ArtinParabolicIntersections`
## 255. Quasi-isometric recognition of virtually polycyclic groups

Proves that every finitely generated group quasi-isometric to a finitely generated virtually polycyclic group is virtually polycyclic, resolving the Eskin–Fisher–Whyte lattice-recognition conjecture. Equivalently, a group quasi-isometric to a lattice in a connected simply connected solvable Lie group is virtually a uniform lattice in some such Lie group, possibly a different one. ([Lean](lean/docs/255.md))

- [Quasi-isometric recognition of virtually polycyclic groups](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf) -- formalized: `PolycyclicRecognition`
## 256. Nonsingular systems of equations over arbitrary groups

Proves that every finite system of equations over an arbitrary group whose exponent-sum matrix has full row rank over ℚ has a simultaneous solution in an overgroup, resolving Howie's conjecture. The coefficient group embeds in the presented quotient. A companion proves Kervaire's conjecture: adjoining one generator and one relation cannot trivialize a nontrivial group. ([Lean](lean/docs/256.md))

- [Nonsingular systems of equations over arbitrary groups](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Nonsingular-systems-of-equations-over-arbitrary-groups-October-5-2026/nonsingular-systems-over-arbitrary-groups.pdf) -- no Lean statement
- [The Kervaire theorem for groups](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Kervaire-Theorem-for-Groups-September-24-2026/The-Kervaire-Theorem-for-Groups-September-24-2026.pdf) -- formalized: `Kervaire`
## 257. A hyperbolic group without a geometric CAT(0) action

Answers negatively whether every word-hyperbolic group is a CAT(0) group. Constructs one with a finite classifying space but no proper cocompact isometric action on any proper complete $`\mathop{\mathrm{CAT}}\nolimits (0)`$ space, in any dimension. ([Lean](lean/docs/257.md))

- [A hyperbolic group with no geometric CAT(0) action](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf) -- formalized: `HyperbolicObstruction`
## 258. Gersten’s conjecture and virtual compact specialness of one-relator groups

Proves Gersten's conjecture: every finitely generated one-relator group containing no Baumslag–Solitar subgroup $`\mathrm{BS}(m,n)`$, with $`m,n\ne0`$, is word-hyperbolic. It also proves that every word-hyperbolic one-relator group is virtually compact special.

- [Baumslag-Solitar-free one-relator groups are hyperbolic](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Baumslag-Solitar-free-one-relator-groups-are-hyperbolic-September-25-2026/paper.pdf) -- no Lean statement
- [Virtual compact specialness of hyperbolic one-relator groups](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Virtual-compact-specialness-of-hyperbolic-one-relator-groups-September-25-2026/paper.pdf) -- no Lean statement
## 259. A group without fixed price

Constructs a finitely generated group with two essentially free probability-measure-preserving actions of different costs, answering the general fixed-price problem negatively. Its Bernoulli action has cost bounded away from one, while a sequence of finite height extensions has costs tending to one.

- [A group without fixed price](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-group-without-fixed-price-October-5-2026/unequal-costs-rank-100-amalgam.pdf) -- no Lean statement
## 260. Spacetime Penrose inequalities: enclosing area, charge, rotation, and anti-de Sitter extensions

Proves the sharp enclosing-area spacetime Penrose inequality for smooth one-ended asymptotically flat initial data in every spatial dimension n ≥ 3, under dominant energy, weak future trapping, positive enclosing area, and the stated decay assumptions. It bounds invariant ADM mass below using minimum enclosing area, with equality rigidity under additional horizon hypotheses. Charged upper-area bounds treat dyonic three-dimensional data; the higher-dimensional purely electric extension uses the matched neutral theorem. ([Lean](lean/docs/260.md))

- [The spacetime Penrose inequality with charge and original-data rigidity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-spacetime-Penrose-inequality-with-charge-and-original-data-rigidity-October-5-2026/paper.pdf) -- no Lean statement
- [A Charged Reduction of the Spacetime Penrose Inequality in Spatial Dimensions at Least Four](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Charged-Reduction-of-the-Spacetime-Penrose-Inequality-in-Spatial-Dimensions-at-Least-Four-October-5-2026/paper.pdf) -- no Lean statement
- [Spacetime Penrose inequalities: enclosing area, charge, and rigidity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Spacetime-Penrose-inequalities-enclosing-area-charge-and-rigidity-October-5-2026/paper.pdf) -- no Lean statement
- [The Kerr–Newman Penrose Inequality for Axisymmetric Electrovacuum Exteriors](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Kerr-Newman-Penrose-Inequality-for-Axisymmetric-Electrovacuum-Exteriors-October-5-2026/paper.pdf) -- no Lean statement
- [Electromagnetic tails and the Kerr–Newman Penrose inequality](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Electromagnetic-tails-and-the-Kerr-Newman-Penrose-inequality-October-5-2026/paper.pdf) -- no Lean statement
- [The nonmaximal anti-de Sitter Penrose Inequality and original-data rigidity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-nonmaximal-anti-de-Sitter-Penrose-Inequality-and-original-data-rigidity-October-5-2026/paper.pdf) -- no Lean statement
- [The Penrose inequality for maximal asymptotically hyperbolic initial data](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Penrose-inequality-for-maximal-asymptotically-hyperbolic-initial-data-October-5-2026/paper.pdf) -- no Lean statement
- [A local Penrose inequality for conformal perturbations of Schwarzschild–anti-de Sitter data](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-local-Penrose-inequality-for-conformal-perturbations-of-Schwarzschild-anti-de-Sitter-data-October-5-2026/paper.pdf) -- no Lean statement
- [The spacetime Penrose inequality and enclosing area](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-spacetime-Penrose-inequality-and-enclosing-area-September-27-2026/paper.pdf) -- no Lean statement
- [Conformal flow and the Riemannian Penrose inequality with minimizing frontiers](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Conformal-flow-and-the-Riemannian-Penrose-inequality-with-minimizing-frontiers-September-27-2026/paper.pdf) -- no Lean statement
- [Equality and rigidity in the spacetime Penrose inequality](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equality-and-rigidity-in-the-spacetime-Penrose-inequality-September-27-2026/paper.pdf) -- no Lean statement
- [Boundary graph deformations for the spacetime Penrose inequality](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Boundary-graph-deformations-for-the-spacetime-Penrose-inequality-September-27-2026/paper.pdf) -- no Lean statement
- [Area-controlled end replacement and the Bondi Penrose inequality in the CKS class](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf) -- formalized: `CKSBondiPenrose`
## 261. Localization and delocalization in the Anderson model

Resolves the predicted spectral contrast for the lattice Anderson model with independent uniform site potentials. In dimension two, every positive disorder strength gives almost surely pure-point spectrum. In every fixed dimension d ≥ 3, sufficiently weak positive disorder gives purely absolutely continuous spectrum on a fixed open interval with nonzero spectral weight. ([Lean](lean/docs/261.md))

- [Absolutely Continuous Spectrum for Weak-Disorder Anderson Models in Dimensions at Least Three](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Absolutely-Continuous-Spectrum-for-Weak-Disorder-Anderson-Models-in-Dimensions-at-Least-Three-September-23-2026/paper.pdf) -- no Lean statement
- [Pure-Point Spectrum for the Two-Dimensional Anderson Model at Every Positive Disorder](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Pure-Point-Spectrum-for-the-Two-Dimensional-Anderson-Model-at-Every-Positive-Disorder-September-23-2026/paper.pdf) -- formalized: `PlanarAndersonSpectrum`
## 262. Sharp finite-matrix Lieb–Thirring inequalities and all equality cases

Proves the sharp one-dimensional Lieb–Thirring inequality for $`1/2\lt \gamma\lt 3/2`$ and arbitrary finite-matrix potentials W ≥ 0 with $`\int\mathop{\mathrm{tr}}\nolimits (W^{\gamma+1/2})\lt \infty`$: the optimal constant is the scalar one-bound-state value, independent of matrix size. All equality cases are direct sums, in one constant unitary basis, of scalar sech2 solitons with independent scales and centers, and zero channels. ([Lean](lean/docs/262.md))

- [Equality cases in the sharp one-dimensional matrix Lieb–Thirring inequality](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equality-cases-in-the-sharp-one-dimensional-matrix-Lieb-Thirring-inequality-October-5-2026/sharp-one-dimensional-lieb-thirring-inequalities-matrix-potentials.pdf) -- no Lean statement
- [Sharp one-dimensional Lieb–Thirring inequalities for matrix potentials](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-one-dimensional-Lieb-Thirring-inequalities-for-matrix-potentials-October-5-2026/sharp-matrix-lieb-thirring.pdf) -- no Lean statement
- [Sharp one-dimensional Lieb–Thirring constants](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-One-Dimensional-Lieb-Thirring-Constants-September-23-2026/paper.pdf) -- formalized: `LiebThirring`
## 263. The ionization and generalized ionization conjectures

For the full nonrelativistic Coulomb model with two electron spin states, proves that a molecule with M fixed nuclei of charges at least one and total charge Z strictly binds at most $`Z+CM`$ electrons. Neutral-atom first ionization energies and radii containing all but an expected half-electron have universal positive upper and lower bounds. The energy cost of removing m electrons has Thomas–Fermi asymptotics as $`m\to\infty`$ and $`Z/m\to\infty`$; neutral-atom outer radii have the corresponding iterated-limit asymptotics, taking $`Z\to\infty`$ first. ([Lean](lean/docs/263.md))

- [Uniform excess charge for Coulomb molecules and the outer radius of neutral atoms](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-excess-charge-for-Coulomb-molecules-and-the-outer-radius-of-neutral-atoms-September-24-2026/paper.pdf) -- no Lean statement
- [Generalized ionization energies for full Coulomb atoms](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf) -- formalized: `CoulombIonization`, `CoulombRadii`
- [Generalized outer-electron radii of neutral Coulomb atoms](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf) -- formalized: `CoulombIonization`, `CoulombRadii`
## 264. Strong cosmic censorship near two-ended Kerr data

Proves local strong cosmic censorship near each fixed rotating subextremal Kerr bridge. A dense Gδ subset of a weighted smooth neighborhood of smooth complete two-ended asymptotically flat vacuum data has full maximal globally hyperbolic developments with no future continuous nondegenerate extension whose weak connection is locally square-integrable. No symmetry is imposed; extensions need not satisfy the vacuum equations.

- [Generic Future Inextendibility with Square-Integrable Connection Near a Fixed Kerr Spacetime](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Generic-Future-Inextendibility-with-Square-Integrable-Connection-Near-a-Fixed-Kerr-Spacetime-September-23-2026/paper.pdf) -- no Lean statement
- [Generic C1 Future Inextendibility Near Rotating Subextremal Kerr Spacetimes](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Generic-C1-Future-Inextendibility-Near-Rotating-Subextremal-Kerr-Spacetimes-September-23-2026/paper.pdf) -- no Lean statement
- [Quantitative Near-Kerr Evolution and Generic C2 Future Inextendibility](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quantitative-Near-Kerr-Evolution-and-Generic-C2-Future-Inextendibility-September-23-2026/paper.pdf) -- no Lean statement
## 265. Area laws and tensor networks for two-dimensional gapped systems

Proves an entropy area law for unique ground states of finite-range Hamiltonians on arbitrary finite induced square-lattice domains, using only a uniform full-system spectral gap and bounds on the local interactions. On open $`L\times L`$ squares, uniformly gapped nearest-neighbor ground states also admit projected entangled-pair state approximations with polynomial bond dimension and global vector error at most L−1.

- [A two-dimensional area law from a global spectral gap](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/paper.pdf) -- no Lean statement
- [Polynomial PEPS approximation of gapped square-grid ground states](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/paper.pdf) -- no Lean statement
## 266. Exactly three mutually unbiased bases in dimension six

Proves $`N(6)=3`$, resolving Zauner's dimension-six mutually unbiased bases conjecture: three such bases exist in ℂ6, but four cannot. The exclusion is a complete certified computation under the stated binary64 arithmetic and compiler conditions. An independent companion proves the Matolcsi–Ruzsa–Weiner Fourier-vanishing conjecture for order-six complex Hadamard matrices outside Tao's cubic equivalence class. ([Lean](lean/docs/266.md))

- [The maximum number of mutually unbiased bases in dimension six](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf) -- formalized: `MUBSix`, `HadamardCubeFiber`
- [Exact Fourier certificates for complex Hadamard matrices of order six](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Fourier-certificates-for-complex-Hadamard-matrices-of-order-six-September-24-2026/Exact-Fourier-certificates-for-complex-Hadamard-matrices-of-order-six-September-24-2026.pdf) -- formalized: `MUBSix`, `HadamardCubeFiber`
## 267. Positive-temperature Bose–Einstein condensation and exact quantum depletion

Proves Bose–Einstein condensation for the exact canonical Gibbs state of the three-dimensional hard-sphere gas: each fixed exclusion distance and sufficiently small fixed density admit a strictly positive temperature, independent of volume, with positive condensate fraction in the thermodynamic limit. At zero temperature, proves the Bogoliubov leading quantum-depletion law for hard spheres and fixed bounded nonnegative radial finite-range potentials of positive scattering length, taking the thermodynamic limit before the dilute limit. ([Lean](lean/docs/267.md))

- [Bose–Einstein condensation at positive temperature in the dilute hard-sphere gas](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Bose-Einstein-condensation-at-positive-temperature-in-the-dilute-hard-sphere-gas-October-5-2026/positive-temperature-hard-spheres.pdf) -- no Lean statement
- [Quantum Depletion and Momentum Distribution in the Dilute Hard-Sphere Bose Gas](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quantum-Depletion-and-Momentum-Distribution-in-the-Dilute-Hard-Sphere-Bose-Gas-October-5-2026/Quantum-Depletion-in-the-Dilute-Hard-Sphere-Bose-Gas.pdf) -- no Lean statement
- [Quantum Depletion for Fixed Bounded Repulsive Potentials](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quantum-Depletion-for-Fixed-Bounded-Repulsive-Potentials-October-5-2026/fixed-repulsion-quantum-depletion.pdf) -- no Lean statement
- [A density-uniform condensate bound for dilute Bose gases](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-density-uniform-condensate-bound-for-dilute-Bose-gases-September-27-2026/paper.pdf) -- no Lean statement
- [Ground-state condensation in the dilute hard-sphere gas](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf) -- formalized: `HardSphere`
## 268. The spin-one Haldane gap

Proves the spin-one Haldane gap conjecture for the pure antiferromagnetic Heisenberg chain on even periodic rings: the spectral gap stays uniformly positive as the chain grows. A companion establishes a gap for odd open chains with endpoint field $`h=3/5`$ and gives boundary-selected infinite-volume states with topological index −1.

- [The periodic spin-one Haldane gap](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-periodic-spin-one-Haldane-gap-September-24-2026/paper.pdf) -- no Lean statement
- [A boundary-field gap for the spin-one Heisenberg chain](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-boundary-field-gap-for-the-spin-one-Heisenberg-chain-September-24-2026/paper.pdf) -- no Lean statement
## 269. Uniform Laughlin gap and stability under bounded scalar disorder

Proves the fermionic Laughlin spectral-gap conjecture for the full V1 interaction at filling 1/3 on the round sphere. The unique ground state remains uniformly gapped under sufficiently weak bounded real scalar one-body potentials projected to the lowest Landau level. Both the gap and disorder threshold are uniform over all sufficiently large particle numbers and all normalized potential profiles. ([Lean](lean/docs/269.md))

- [Uniform Stability of the Spherical Laughlin Gap](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf) -- formalized: `LaughlinGap`, `Laughlin`, `LaughlinFock`, `LaughlinPlanar`
- [A Fock-space inequality and the Laughlin spectral gap](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf) -- formalized: `LaughlinGap`, `Laughlin`, `LaughlinFock`, `LaughlinPlanar`
## 270. Threshold and positive-energy bound states of the BFSS matrix model

Proves that the undeformed relative $`\mathrm{SU}(N)`$ BFSS model has exactly one normalizable zero-energy state for every finite N ≥ 2, resolving the threshold-bound-state conjecture. For $`\mathrm{SU}(2)`$, a companion proves infinitely many normalizable positive-energy eigenstates with unbounded energies, contradicting the original BFSS paper's exclusion of additional bound states at N = 2.

- [The unique threshold bound state of the SU(N) BFSS model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-unique-threshold-bound-state-of-the-SU-N-BFSS-model-September-24-2026/paper.pdf) -- no Lean statement
- [Positive eigenvalues of the relative SU(2) BFSS Hamiltonian](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Positive-eigenvalues-of-the-relative-SU-2-BFSS-Hamiltonian-October-5-2026/positive-eigenvalues-relative-su2-bfss.pdf) -- no Lean statement
## 271. Bloch's law, its lattice correction, and the spherical magnetization law

Proves Bloch's T3/2 law with its exact coefficient for three-dimensional quantum Heisenberg ferromagnets at every positive quantum spin, allowing nonnegative symmetric finite-range couplings whose support generates ℤ3. The thermodynamic limit precedes the zero-field derivative and low-temperature limit. The family also proves spontaneous magnetization for nearest-neighbor models in every dimension d ≥ 3 and determines the first lattice correction for three-dimensional nearest-neighbor couplings. ([Lean](lean/docs/271.md))

- [Bloch's Law for Finite-Range Heisenberg Ferromagnets in Three Dimensions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Blochs-Law-for-Finite-Range-Heisenberg-Ferromagnets-in-Three-Dimensions-October-5-2026/bloch-law-heisenberg.pdf) -- no Lean statement
- [The first lattice correction to Bloch's law](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-first-lattice-correction-to-Blochs-law-October-5-2026/first-lattice-correction-bloch-law.pdf) -- no Lean statement
- [The spherical magnetization law for the three-dimensional quantum Heisenberg ferromagnet](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-spherical-magnetization-law-for-the-three-dimensional-quantum-Heisenberg-ferromagnet-October-5-2026/spherical-magnetization.pdf) -- no Lean statement
- [Spontaneous magnetization in the quantum Heisenberg ferromagnet](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Spontaneous-magnetization-in-the-quantum-Heisenberg-ferromagnet-September-24-2026/paper.pdf) -- formalized: `Heisenberg`
## 272. Entanglement without distillable secret key

Constructs an entangled state on $`\mathbb C^{10}\otimes\mathbb C^{10}`$ with zero distillable secret key for the specified local-instrument protocols that complete almost surely. These allow joint local processing and authenticated two-way public communication, with no other shared private resource and an eavesdropper holding the input purification and public record. A trace-preserving PPT channel on $`M_{21}(\mathbb C)`$ whose square is not entanglement breaking disproves Christandl's PPT-square conjecture. ([Lean](lean/docs/272.md))

- [Entanglement with zero distillable secret key in local dimension ten](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf) -- formalized: `DimensionTenChannel`, `DimensionTenPair`
## 273. The entropy photon-number inequality

Proves the entropy photon-number inequality for beam-splitter mixing of two independent finite-energy bosonic inputs in any finite number of modes: the output's entropy photon number is at least the transmissivity-weighted average of the inputs'. Arbitrary entanglement within each input is allowed, and product thermal inputs attain equality even when their entropies differ. ([Lean](lean/docs/273.md))

- [The entropy photon-number inequality](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-entropy-photon-number-inequality-September-24-2026/paper.pdf) -- formalized: `EntropyPhotonNumber`
## 274. Parity is not in QAC<sup>0</sup>

Resolves Moore's parity conjecture in the measured-output model: constant-depth quantum circuits with arbitrary one-qubit gates, unbounded-arity Toffoli gates and polynomially many total qubits cannot compute parity with any fixed positive worst-case advantage. Ancillas start in zero, one output qubit is measured, and all other registers may be discarded. Xu–Li's reductions give the same bounded-error obstruction for strict majority. ([Lean](lean/docs/274.md))

- [Product-projection localization and the QAC0 parity lower bound](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Product-projection-localization-and-the-QAC0-parity-lower-bound-September-24-2026/paper.pdf) -- formalized: `QACParity`, `RegularParity`
- [Regular trajectories, pruning and quantum parity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Regular-trajectories-pruning-and-quantum-parity-September-24-2026/paper.pdf) -- formalized: `QACParity`, `RegularParity`
## 275. QMA-hardness of continuum Coulomb energy

Proves QMA-hardness of approximating the electronic Coulomb energy infimum in three dimensions, minimizing over the full spinful fermionic continuum space. Deterministic polynomial-time reductions work even with only unit-charge nuclei at distinct rational positions, polynomially many electrons and an energy-threshold separation of at least one. ([Lean](lean/docs/275.md))

- [Continuum Coulomb hardness with binary nuclear charges](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf) -- formalized: `ContinuumCoulombHardness`
- [QMA-hardness of continuum Coulomb energy with unit nuclear charges](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/QMA-hardness-of-continuum-Coulomb-energy-with-unit-nuclear-charges-September-24-2026/QMA-hardness-of-continuum-Coulomb-energy-with-unit-nuclear-charges-September-24-2026.pdf) -- formalized: `ContinuumCoulombHardness`
## 276. Classical capacity of generalized amplitude damping

Determines the unassisted classical capacity of every qubit generalized amplitude-damping channel, including all damping and thermal parameters. An explicit one-variable optimization gives the capacity, attained by independent two-state signal ensembles with collective decoding. Holevo capacity, minimum output entropy and regularized classical capacity are additive when tensoring with any finite-dimensional quantum channel. ([Lean](lean/docs/276.md))

- [Classical capacity and entropy inequalities for generalized amplitude damping](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/paper.pdf) -- formalized: `AmplitudeDamping`
## 277. Threshold repetition for entangled games

Proves exponential threshold repetition for every finite two-player one-round game: if its entangled value is v &lt; 1, the probability of winning at least a fraction $`v+\delta`$ of k independent repetitions decays exponentially in k, for $`0\lt \delta\lt 1-v`$. Arbitrary joint finite-dimensional entangled strategies and correlated question distributions are allowed. ([Lean](lean/docs/277.md))

- [Threshold parallel repetition for finite-dimensional entangled games](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Threshold-parallel-repetition-for-finite-dimensional-entangled-games-September-25-2026/paper.pdf) -- formalized: `EntangledGames`
## 278. Failure of Kohn–Sham ensemble representation

Constructs a three-electron Coulomb molecule with two equal positive-integer-charge nuclei whose absolute ground-state density has no noninteracting ground-state ensemble representation by a single real spin-independent local potential in $`L^{3/2}(\mathbb R^3)+L^\infty(\mathbb R^3)`$. This disproves Kohn–Sham ensemble representability for that potential class; the required nuclear charge is specified nonnumerically.

- [A Coulomb ground-state density without Kohn-Sham ensemble representation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Coulomb-Ground-State-Density-without-Kohn-Sham-Ensemble-Representation-September-25-2026/paper.pdf) -- no Lean statement
## 279. Exact quantum factoring over a fixed finite gate set

Gives a polynomial-time uniform quantum circuit family that outputs the complete prime factorization of every integer with probability one. Both gate count and qubit count are polynomial in the input length, and one fixed finite gate set suffices. ([Lean](lean/docs/279.md))

- [Exact quantum factoring over a fixed finite gate set](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf) -- formalized: `ExactQuantumFactoring`
## 280. Unitary vertex operator algebras and conformal nets

Proves the strongly rational case of the strong-locality conjecture: every simple unitary strongly rational complex vertex operator algebra generates a completely rational conformal net. Its simple modules are unitarizable, and its representation category agrees with the net’s finite-index sectors as a braided unitary tensor category. ([Lean](lean/docs/280.md))

- [Strongly rational unitary vertex operator algebras and conformal nets](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Strongly-rational-unitary-vertex-operator-algebras-and-conformal-nets-September-25-2026/paper.pdf) -- formalized: `VertexAlgebraNet`
## 281. QAOA attains the SK optimum in the thermodynamic-first limit

Proves that QAOA approaches the ground-state energy of the Gaussian zero-field Sherrington–Kirkpatrick model when system size tends to infinity before circuit depth. For every accuracy, finite depth and deterministic angles independent of size and disorder achieve the required limiting expected energy per spin. This also yields leading-order optimal expected MaxCut values on large-degree random regular graphs, with size tending to infinity before degree. ([Lean](lean/docs/281.md))

- [QAOA attains the SK ground-state energy in the thermodynamic-first limit](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf) -- formalized: `SKValue`, `SKFullSupport`
- [Full support of the zero-temperature Sherrington-Kirkpatrick order parameter](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf) -- formalized: `SKValue`, `SKFullSupport`
## 282. From scale symmetry to local conformal symmetry in four-dimensional QFT

Under the stated bounded-local-net and field-reconstruction hypotheses, proves that scale symmetry implies local conformal symmetry for four-dimensional unitary positive-energy theories with a discrete bounded-below scaling spectrum of finite multiplicity, finite scaling support and a physical local scale current. The stress tensor has a traceless improvement with unchanged spacetime charges. The conclusion concerns local Ward identities, not a global conformal action on the whole net.

- [Scale and conformal symmetry in four-dimensional operational quantum field theory](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Scale-and-conformal-symmetry-in-four-dimensional-operational-quantum-field-theory-September-26-2026/main.pdf) -- no Lean statement
## 283. Polynomial-time unitary synthesis from a Boolean oracle

Solves the constant-error Aaronson–Kuperberg unitary synthesis problem: a uniform polynomial-size quantum oracle circuit approximates every n-qubit unitary channel within diamond-norm error 1/2, after a suitable Boolean oracle is chosen. Gates, qubits, oracle calls and query length are polynomially bounded. The target-dependent oracle may have an unrestricted truth table; its efficient classical construction is not asserted.

- [Polynomial-Time Unitary Synthesis from a Boolean Oracle](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Polynomial-Time-Unitary-Synthesis-from-a-Boolean-Oracle-October-5-2026/paper.pdf) -- no Lean statement
## 284. The optimal quartic separation between randomized and quantum queries

Shows that the universal bound $`R(f)=O((1+Q(f))^4)`$ for total Boolean functions is sharp in its exponent, ruling out every smaller power and disproving the conjectured cubic relation. Here R and Q are randomized and quantum worst-case bit-query complexities with error at most 1/3; computation between queries is unrestricted.

- [A Nearly Quartic Separation Between Randomized and Quantum Query Complexity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Nearly-Quartic-Separation-Between-Randomized-and-Quantum-Query-Complexity-October-5-2026/quartic-query-separation.pdf) -- no Lean statement
## 285. Counterexamples to Baum–Connes and Kadison–Kaplansky

Disproves the coefficient-free reduced Baum–Connes conjecture through a failure of rational injectivity and a separate failure of surjectivity of assembly. A finitely generated torsion-free example witnesses the injectivity failure. Separately, a torsion-free group has a nontrivial projection in its reduced group C∗-algebra, disproving the Kadison–Kaplansky conjecture.

- [A torsion-free counterexample to reduced Baum–Connes injectivity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Torsion-Free-Counterexample-to-Reduced-Baum-Connes-Injectivity-September-23-2026/paper.pdf) -- no Lean statement
- [A torsion-free counterexample to the Kadison–Kaplansky projection conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Torsion-Free-Counterexample-to-the-Kadison-Kaplansky-Projection-Conjecture-September-23-2026/paper.pdf) -- no Lean statement
- [An irrational-trace counterexample to reduced Baum–Connes](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-Irrational-Trace-Counterexample-to-Reduced-Baum-Connes-September-23-2026/paper.pdf) -- no Lean statement
## 286. Rigidity and arithmetic of lattice von Neumann algebras

Classifies finite-index bimodules between scalar-twisted group factors of ICC groups commensurable with property-$`(T)`$ lattices over characteristic-zero local fields and arbitrary ICC group factors. Every such bimodule is a summand of finite sums of models arising from finite-index subgroup isomorphisms and finite-dimensional projective representations. The classification also recovers the group, scalar cocycle and amplification scale up to the stated stable equivalence.

- [Arithmeticity of twisted finite correspondences for lattices over local fields](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Arithmeticity-of-twisted-finite-correspondences-for-lattices-over-local-fields-September-23-2026/paper.pdf) -- no Lean statement
- [The arithmetic category and stable recovery of lattice factors](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-arithmetic-category-and-stable-recovery-of-lattice-factors-September-23-2026/paper.pdf) -- no Lean statement
## 287. Isomorphism of the free group factors

Resolves the free group factor isomorphism problem: $`L(\mathbb F_2)\cong L(\mathbb F_3)`$, and hence all interpolated free group factors, including $`L(\mathbb F_\infty)`$, are isomorphic. Their common factor has fundamental group $`\mathbb R_{\gt 0}`$. ([Lean](lean/docs/287.md))

- [An isomorphism of the free group factors](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf) -- formalized: `InterpolatedFactors`
## 288. Kadison's similarity conjecture

Proves Kadison's similarity conjecture: every bounded complex-linear unital algebra homomorphism from a unital complex C∗-algebra to operators on a Hilbert space becomes a $`*`$-homomorphism after conjugation by a bounded invertible operator. ([Lean](lean/docs/288.md))

- [Kadison's similarity theorem through uniform derivation estimates](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf) -- formalized: `KadisonSimilarity`, `UniformCommutator`
## 289. Strong Kadison–Kastler stability and its spatial boundaries

Proves that sufficiently close unital von Neumann algebras on the same Hilbert space are conjugate by a unitary arbitrarily close to the identity, with a universal tolerance in the operator-norm distance between unit balls. Counterexamples show that near-identity conjugacy fails for one-sided near inclusions, and that arbitrarily close norm-separable C∗-algebras need not be ambiently unitarily conjugate. ([Lean](lean/docs/289.md))

- [Universal strong Kadison–Kastler stability](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf) -- formalized: `StrongKadisonKastler`
- [Near Inclusions of von Neumann Algebras Without Small Spatial Embeddings](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Near-Inclusions-of-von-Neumann-Algebras-Without-Small-Spatial-Embeddings-October-5-2026/near-inclusions.pdf) -- no Lean statement
- [Close Separable C*-Algebras Without Spatial Conjugacy](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Close-Separable-Cstar-Algebras-Without-Spatial-Conjugacy-October-5-2026/paper.pdf) -- no Lean statement
## 290. Relative bicentralizers and modular spectral recovery

Proves Connes' bicentralizer conjecture for every type III1 factor with separable predual and every faithful normal state. More generally, for every inclusion $`N\subset M`$ of von Neumann algebras with separable preduals admitting a faithful normal conditional expectation, constructs an amenable expected subalgebra $`P\subset N`$ with $`P'\cap c(M)=N'\cap c(M)`$, resolving the relative bicentralizer conjecture. ([Lean](lean/docs/290.md))

- [Expected amenable subalgebras preserving core commutants](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Expected-amenable-subalgebras-preserving-core-commutants-September-23-2026/Expected-amenable-subalgebras-preserving-core-commutants-September-23-2026.pdf) -- no Lean statement
- [Bounded recovery for modular spectral averages](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Bounded-recovery-for-modular-spectral-averages-September-23-2026/Bounded-recovery-for-modular-spectral-averages-September-23-2026.pdf) -- formalized: `BoundedRecovery`
## 291. Cuntz comparison, nuclear dimension, and equivariant Jiang–Su stability

Proves equivariant Jiang–Su stability for every countable discrete amenable group action on a simple separable unital infinite-dimensional nuclear stably finite Jiang–Su-stable C∗-algebra, resolving this case of Szabó's conjecture without restrictions on trace dynamics. The family also proves the unital Toms–Winter conjecture, equating strict comparison, finite nuclear dimension and Jiang–Su stability in the simple separable unital infinite-dimensional nuclear setting. ([Lean](lean/docs/291.md))

- [Equivariant Jiang–Su Stability for Amenable Actions in the Unital Stably Finite Case](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equivariant-Jiang-Su-Stability-for-Amenable-Actions-in-the-Unital-Stably-Finite-Case-October-5-2026/paper.pdf) -- no Lean statement
- [Cuntz comparison and Jiang–Su absorption](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Cuntz-comparison-and-Jiang-Su-absorption-September-23-2026/paper.pdf) -- no Lean statement
- [Nuclear dimension and Jiang–Su stability without elementary subquotients](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Nuclear-dimension-and-Jiang-Su-stability-without-elementary-subquotients-September-23-2026/paper.pdf) -- no Lean statement
- [Tracial projection methods and uniform property Gamma](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Tracial-projection-methods-and-uniform-property-Gamma-September-23-2026/paper.pdf) -- formalized: `UniformGamma`
## 292. Kirchberg's $`\mathcal O_2`$ norm-ultrapower embedding problem

Constructs an explicit separable unital full group C∗-algebra that cannot embed unitally into the norm ultrapower of any fixed nonzero unital nuclear C∗-algebra, for any free ultrafilter on the natural numbers. Taking the target to be $`\mathcal O_2`$ answers Kirchberg's norm-ultrapower embedding problem negatively. ([Lean](lean/docs/292.md))

- [An explicit obstruction to nuclear norm-ultrapower embeddings](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-obstruction-to-nuclear-norm-ultrapower-embeddings-September-23-2026/paper.pdf) -- formalized: `NuclearUltrapower`
## 293. Invariant projections, hyperinvariant subspaces, and transitive algebras

Constructs a nonzero norm-quasinilpotent operator on every infinite-dimensional separable complex Hilbert space with no nonzero proper closed subspace invariant under every commuting operator. The construction also gives operators with no nontrivial invariant projection in the hyperfinite type II1 factor. ([Lean](lean/docs/293.md))

- [Invariant-projection counterexamples for every irrational rotation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf) -- formalized: `FiniteFactor`, `BackwardIntertwiners`, `ContinuousCircleWeight`, `HyperinvariantSubspaces`, `IrrationalRotation`, `ProductBrown`
- [Backward intertwiners and a transitive commutant](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Backward-intertwiners-and-a-transitive-commutant-September-27-2026/paper.pdf) -- formalized: `FiniteFactor`, `BackwardIntertwiners`, `ContinuousCircleWeight`, `HyperinvariantSubspaces`, `IrrationalRotation`, `ProductBrown`
## 294. Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness

Disproves Kaplansky's quasitrace conjecture by constructing a separable unital complex C∗-algebra admitting normalized 2-quasitraces, all of which are nonadditive. As a consequence, two unital simple stably finite C∗-algebras can have a properly infinite minimal tensor product, with one factor $`C_r^*(\mathbb F_2)`$. ([Lean](lean/docs/294.md))

- [A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf) -- formalized: `KaplanskyQuasitrace`, `KaplanskyStableFiniteness`
## 295. The Kadison–Ringrose cohomology conjecture

Proves that every bounded Hochschild cocycle of degree at least two on a complex von Neumann algebra, with coefficients in the algebra itself, has a bounded primitive. Equivalently, all higher bounded Hochschild cohomology groups vanish, resolving the Kadison–Ringrose conjecture. ([Lean](lean/docs/295.md))

- [Vanishing of higher bounded Hochschild cohomology](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf) -- formalized: `KadisonRingrose`
## 296. The generator problem for finite factors

Proves that every type II1 factor with separable predual is generated by a single operator, equivalently by two self-adjoint operators, resolving the generator problem. More strongly, for every irreducible inclusion $`P\subset M`$ of such factors, the unitaries u with $`M=W^*(P,u)`$ form a dense Gδ subset in the trace 2-norm topology. ([Lean](lean/docs/296.md))

- [Relative generation and the generator problem for finite factors](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf) -- formalized: `FactorGeneration`, `RelativeGeneration`
## 297. A ZFC counterexample to Naimark's problem

Gives an alternative to [Tanaka's ZFC construction](https://arxiv.org/abs/2609.26930v1) of a unital infinite-dimensional simple complex C∗-algebra with a faithful tracial state and exactly one nonzero irreducible representation up to unitary equivalence. Thus the unrestricted compact-operator characterization fails without additional set-theoretic assumptions; the counterexample is nonseparable. ([Lean](lean/docs/297.md))

- [A counterexample to Naimark's problem in ZFC](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf) -- formalized: `Naimark`
## 298. Two notions of free entropy differ even when both are finite

Constructs a bounded self-adjoint tuple in a tracial von Neumann algebra whose microstates and nonmicrostates free entropies satisfy $`-\infty\lt \chi\lt \chi^*\lt \infty`$. This answers Voiculescu’s finite-entropy equality question negatively: the matrix-approximation and free-Fisher-information definitions differ even when both are finite. ([Lean](lean/docs/298.md))

- [A finite-entropy separation of microstates and nonmicrostates free entropy](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-finite-entropy-separation-of-microstates-and-nonmicrostates-free-entropy-September-25-2026/paper.pdf) -- formalized: `FiniteEntropySeparation`
## 299. The Kirchberg–Rørdam character criterion and infinite tensor-power Jiang–Su stability

A nonzero unital separable complex C∗-algebra is Jiang–Su stable exactly when its norm central-sequence algebra has no characters, for every free ultrafilter. This answers the Kirchberg–Rørdam character question. Also, the infinite minimal tensor power of every such algebra without characters is Jiang–Su stable, answering the Dadarlat–Toms question. ([Lean](lean/docs/299.md))

- [The Kirchberg–Rørdam character criterion](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf) -- formalized: `CharacterCriterion`
## 300. Approximation and quadratic strong-operator paving

Proves that every self-adjoint element of a complex von Neumann algebra admits strong-operator paving relative to any maximal abelian subalgebra with $`O(\varepsilon^{-2})`$ blocks. The norm bound holds after compression by a projection arbitrarily close to the identity in the strong topology, resolving the Popa–Vaes quadratic paving conjecture.

- [Approximation Paving over Arbitrary Maximal Abelian Subalgebras](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Approximation-Paving-over-Arbitrary-Maximal-Abelian-Subalgebras-September-25-2026/Approximation-Paving-over-Arbitrary-Maximal-Abelian-Subalgebras-September-25-2026.pdf) -- no Lean statement
- [Quadratic Strong-Operator Paving over Arbitrary Maximal Abelian Subalgebras](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quadratic-Strong-Operator-Paving-over-Arbitrary-Maximal-Abelian-Subalgebras-September-25-2026/Quadratic-Strong-Operator-Paving-over-Arbitrary-Maximal-Abelian-Subalgebras-September-25-2026.pdf) -- no Lean statement
## 301. Trace cones and Razak–Jacelon stabilization

Classifies separable nuclear complex C∗-algebras after tensoring with the Razak–Jacelon algebra and the compact operators, using their full topological cones of extended lower-semicontinuous tracial weights. This answers Robert’s trace-cone question, including algebras with arbitrary ideal structure and both finite and infinite subquotients. ([Lean](lean/docs/301.md))

- [The trace cone classifies Razak–Jacelon stabilizations](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-trace-cone-classifies-Razak-Jacelon-stabilizations-September-25-2026/The-trace-cone-classifies-Razak-Jacelon-stabilizations-September-25-2026.pdf) -- formalized: `TraceIdealTransportSupport`
## 302. Radius of comparison equals half the mean dimension

For every minimal homeomorphism h of an infinite compact metrizable space X, the radius of comparison of $`C(X)\rtimes_h\mathbb Z`$ equals $`\tfrac12\mathrm{mdim}(X,h)`$, including infinite values. Zero mean dimension is equivalent to the small boundary property, Jiang–Su stability and finite nuclear dimension; in this case nuclear dimension is at most one.

- [Filtered products and boundary-preserving compression in complex cobordism](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Filtered-products-and-boundary-preserving-compression-in-complex-cobordism-September-25-2026/paper.pdf) -- no Lean statement
- [Radius of comparison equals half the mean dimension](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Radius-of-comparison-equals-half-the-mean-dimension-September-25-2026/paper.pdf) -- no Lean statement
## 303. Weak pure infiniteness and Cuntz-algebra absorption

Resolves the ordinary-to-strong pure-infiniteness question of Kirchberg and Rørdam for complex C∗-algebras. For exact algebras, proper infiniteness of one fixed finite amplification of every positive element also suffices. Consequently, every separable nuclear algebra with this property absorbs $`\mathcal O_\infty`$, without unitality or simplicity assumptions. ([Lean](lean/docs/303.md))

- [Weak pure infiniteness and O-infinity absorption](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf) -- formalized: `ExactInfiniteness`, `IndividualStrongInfiniteness`
## 304. The Hilbert–Smith conjecture in every dimension

Every locally compact second-countable Hausdorff group acting faithfully and jointly continuously on a connected finite-dimensional topological manifold is a Lie group. This proves the Hilbert–Smith conjecture in all finite dimensions, for Hausdorff second-countable manifolds without boundary.

- [The Hilbert–Smith conjecture in every finite dimension](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/paper.pdf) -- no Lean statement
## 305. Four-dimensional disk embedding and Wall's conjecture

The unrestricted four-dimensional disk-embedding conjecture fails: framed algebraic dual spheres do not suffice to obtain disjoint locally flat spanning disks. In particular, the free group F2 is not good in the sense of Freedman–Quinn. Also constructs a finitely presented integral Poincaré duality group of dimension four with a finite classifying space but no realization as the fundamental group of a closed aspherical topological four-manifold, disproving Wall's conjecture.

- [A boundary-only obstruction to four-dimensional disk embedding](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-boundary-only-obstruction-to-four-dimensional-disk-embedding-September-24-2026/paper.pdf) -- no Lean statement
- [A marked tensor obstruction to four-dimensional disk embedding](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-marked-tensor-obstruction-to-four-dimensional-disk-embedding-September-24-2026/paper.pdf) -- no Lean statement
- [A PD4 group without an aspherical manifold model](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-PD4-group-without-an-aspherical-manifold-model-September-24-2026/paper.pdf) -- no Lean statement
## 306. The purely cosmetic surgery conjecture

Distinct Dehn surgery slopes on a nontrivial smooth knot in S3 never produce orientation-preservingly homeomorphic manifolds, proving the purely cosmetic surgery conjecture. The statement includes the meridional slope.

- [Purely cosmetic surgery on knots in the three-sphere](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Purely-Cosmetic-Surgery-on-Knots-in-the-Three-Sphere-September-23-2026/paper.pdf) -- no Lean statement
## 307. Failure of rational injectivity for maximal coarse assembly

Constructs a uniformly discrete bounded-geometry space whose maximal coarse assembly map is not rationally injective. The example is a coarse disjoint union of finite connected graphs of uniformly bounded degree, with an infinite-order kernel class. A companion gives the analogous failure for reduced coarse assembly, disproving the rational coarse Novikov conjecture. ([Lean](lean/docs/307.md))

- [Failure of rational injectivity for maximal coarse assembly](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Failure-of-rational-injectivity-for-maximal-coarse-assembly-October-5-2026/paper.pdf) -- no Lean statement
- [A counterexample to the coarse Novikov conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-the-coarse-Novikov-conjecture-September-23-2026/paper.pdf) -- formalized: `CoarseAssembly`
## 308. Finite Smith–Toda complexes at every height

For every n ≥ 0, constructs a finite Smith–Toda spectrum at a prime p depending on n, with Brown–Peterson homology $`BP_*/(p,v_1,\ldots,v_n)`$ and the canonical comodule structure. Thus Smith–Toda complexes exist at every height when the prime may vary; an explicit example realizes $`V(4)`$ at p = 1009.

- [Finite Smith–Toda Complexes at Varying Primes](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-Smith-Toda-Complexes-at-Varying-Primes-September-23-2026/paper.pdf) -- no Lean statement
- [A finite Smith–Toda complex V(4) at the prime 1009](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-finite-Smith-Toda-complex-V4-at-the-prime-1009-September-23-2026/paper.pdf) -- no Lean statement
## 309. The Kervaire invariant problem at the prime three

Resolves the odd-primary Kervaire invariant problem at the prime three: exactly the standard classes with indices 0, 2, and 3 survive in the mod-three Adams spectral sequence, in stems 10, 106, and 322. Each surviving detection coset contains an element of exact additive order three.

- [The Kervaire invariant problem at the prime three](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Kervaire-Invariant-Problem-at-the-Prime-Three-September-24-2026/paper.pdf) -- no Lean statement
## 310. Quillen's conjecture in rational homology

Proves the rational-homology form of Quillen's conjecture for every finite group and every prime. If the largest normal p-subgroup of G is trivial, the poset of nontrivial elementary abelian p-subgroups has nonzero augmented reduced rational homology and is therefore not contractible.

- [Rational homology and Quillen's conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Rational-homology-and-Quillens-conjecture-September-24-2026/paper.pdf) -- no Lean statement
## 311. The Hovey–Strickland and Chai conjectures

Proves Chai's invariant-ideal conjecture for Lubin–Tate deformation rings over finite residue fields, at every prime and positive height n. Through the implication of Barthel–Heard–Naumann, this proves the Hovey–Strickland conjecture: dualizable $`K(n)`$-local spectra have exactly $`n+2`$ thick tensor ideals, and their Balmer spectrum is a chain of $`n+1`$ points.

- [Stabilizer orbits and thick tensor ideals of dualizable K(n)-local spectra](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Stabilizer-Orbits-and-Thick-Tensor-Ideals-of-Dualizable-Kn-Local-Spectra-September-24-2026/paper.pdf) -- no Lean statement
## 312. The Grothendieck homotopy hypothesis

Proves the Grothendieck homotopy hypothesis for ∞-groupoids associated with every Grothendieck coherator in the Ara–Henry convention: these algebraic objects recover the homotopy theory of spaces. ([Lean](lean/docs/312.md))

- [The Grothendieck homotopy hypothesis via elementary expansions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Grothendieck-homotopy-hypothesis-via-elementary-expansions-September-24-2026/paper.pdf) -- formalized: `GrothendieckElementaryExpansion`
## 313. Finite generation for the $`K(n)`$-local sphere

Answers the degreewise finiteness question of Hovey and Hovey–Strickland: every homotopy group of the $`K(n)`$-local sphere is a finitely generated ℤp-module, for every prime, positive height and integer degree. The same conclusion holds after $`K(n)`$-localizing any finite p-local spectrum.

- [Finite generation for the K(n)-local sphere](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-generation-for-the-Kn-local-sphere-September-24-2026/Finite-generation-for-the-Kn-local-sphere-September-24-2026.pdf) -- no Lean statement
## 314. Cyclic length and chromatic fixed-point loss

Determines the optimal chromatic loss from geometric H-fixed points to geometric G-fixed points for every subgroup H of a finite p-group G. At every nonnegative height, the loss equals the shortest subnormal-chain length from H to G with cyclic quotients. Each quotient counts once regardless of order, and finite spectra witness sharpness.

- [Cyclic length and chromatic fixed-point loss](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Cyclic-Length-and-Chromatic-Fixed-Point-Loss-September-24-2026/Cyclic-Length-and-Chromatic-Fixed-Point-Loss-September-24-2026.pdf) -- no Lean statement
## 315. The four-dimensional Singer conjecture

Proves that the L2-Betti numbers of the universal cover of every closed connected aspherical topological four-manifold vanish outside degree two. More generally, the same conclusion holds for every finite connected aspherical integral Poincaré complex of formal dimension four, proving the four-dimensional Singer conjecture in this wider class.

- [The Singer conjecture in dimension four](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Singer-conjecture-in-dimension-four-September-25-2026/paper.pdf) -- no Lean statement
## 316. Curtis’s conjecture

Proves Curtis’s conjecture: the positive-degree mod-two stable Hurewicz image of the sphere is spanned by the images of the Hopf-invariant-one classes η, ν, σ and the Kervaire-invariant-one classes that exist.

- [The Stable Hurewicz Image of the Sphere at Two](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Stable-Hurewicz-Image-of-the-Sphere-at-Two-September-25-2026/paper.pdf) -- no Lean statement
## 317. Thomason model structures in all strict higher dimensions

Resolves the Ara–Maltsiniotis conjecture: for every n ≥ 1 and n = ω, small strict globular n-categories admit proper combinatorial Thomason model structures Quillen equivalent to simplicial sets. Thus strict higher categories model the homotopy theory of spaces in every stated dimension. ([Lean](lean/docs/317.md))

- [Thomason Model Structures in Every Strict Higher Dimension](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/paper.pdf) -- formalized: `ThomasonModelStructures`
## 318. Chromatic splitting: filtrations and counterexamples

Disproves strong chromatic splitting at height three for primes p ≥ 5, and weak splitting for the derived p-completed sphere at heights p (p ≥ 5) and $`p+1`$ (p ≥ 7). Nevertheless, for n ≥ 1 and $`p\gt n+1`$, the overlap $`L_{n-1}L_{K(n)}S_p^\wedge`$ admits a $`2^n`$-stage filtration by the predicted localized-sphere pieces. At height three and prime three, even finite assembly from such pieces fails in the category of $`E(2)`$-local modules over the derived completed sphere.

- [Filtered chromatic splitting at generic primes](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Filtered-chromatic-splitting-at-generic-primes-September-25-2026/paper.pdf) -- no Lean statement
- [The height-three chromatic overlap: an explicit filtration and its attachments](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-height-three-chromatic-overlap-an-explicit-filtration-and-its-attachments-September-27-2026/paper.pdf) -- no Lean statement
- [A rational obstruction to strong chromatic splitting at height three](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-rational-obstruction-to-strong-chromatic-splitting-at-height-three-September-25-2026/paper.pdf) -- no Lean statement
- [Failure of finite assembly for a chromatic overlap at the prime three](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Failure-of-finite-assembly-for-a-chromatic-overlap-at-the-prime-three-September-25-2026/paper.pdf) -- no Lean statement
- [Counterexamples to weak chromatic splitting: sphere kernels and descent exponents](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Counterexamples-to-weak-chromatic-splitting-sphere-kernels-and-descent-exponents-September-27-2026/paper.pdf) -- no Lean statement
## 319. Counterexamples to finite generation at chromatic height two

Refutes the Hahn–Wilson conjecture at chromatic height two. For every sufficiently large prime p, constructs a connective p-complete spectrum of exact fp-type two that cannot be built from completed $`\mathrm{BP}\langle2\rangle`$ by finitely many sums, shifts, cones and retracts. The examples nevertheless satisfy the finite and telescopic localization comparisons.

- [Counterexamples to the Hahn-Wilson conjecture at height two](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Counterexamples-to-the-Hahn-Wilson-conjecture-at-height-two-September-26-2026/paper.pdf) -- no Lean statement
## 320. Nonhomeomorphic closed aspherical four-manifolds

Constructs closed connected aspherical topological four-manifolds that are homotopy equivalent but not homeomorphic, with a common word-hyperbolic fundamental group. This disproves even the homeomorphism-existence formulation of the Borel conjecture in dimension four.

- [Nonhomeomorphic closed aspherical four-manifolds with the same homotopy type](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Nonhomeomorphic-closed-aspherical-four-manifolds-with-the-same-homotopy-type-October-4-2026/paper.pdf) -- no Lean statement
## 321. A counterexample to Wall's finite D(2) problem

Constructs a finite connected three-dimensional CW complex whose universal cover has no integral homology above degree two and whose third cohomology vanishes for every local coefficient module, but which has no finite two-dimensional homotopy model. This disproves Wall's finite D(2) conjecture; the example has infinite fundamental group.

- [A Counterexample to Wall's D(2) Problem](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/wall-d2-counterexample.pdf) -- no Lean statement
## 322. Tingley’s sphere-isometry problem

Resolves Tingley's problem: every surjective isometry between the unit spheres of nonzero real Banach spaces extends uniquely to a surjective real-linear isometry of the whole spaces. No dimension restriction is imposed, so the metric geometry of the unit sphere determines the Banach space up to linear isometry. ([Lean](lean/docs/322.md))

- [A positive solution to Tingley’s problem](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-positive-solution-to-Tingleys-problem-September-23-2026/paper.pdf) -- formalized: `TingleySphereIsometry`
## 323. Independence of the separable quotient problem

Establishes, relative to the consistency of a measurable cardinal, that the separable quotient problem is independent of ZFC. The assertion that every infinite-dimensional Banach space has a separable infinite-dimensional quotient can hold for all real and complex Banach spaces, whereas the continuum hypothesis yields counterexamples over both fields. ([Lean](lean/docs/323.md))

- [Relative independence of the separable quotient problem](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/paper.pdf) -- formalized: `SeparableQuotientNegative`
## 324. Lipschitz equivalent Banach spaces need not be linearly isomorphic

Constructs separable real Banach spaces that are globally bi-Lipschitz equivalent but not linearly isomorphic, resolving the separable Lipschitz-isomorphism problem negatively. Thus even the complete metric structure up to bi-Lipschitz equivalence does not determine a separable Banach space's linear isomorphism class. ([Lean](lean/docs/324.md))

- [Lipschitz Equivalent Separable Banach Spaces Need Not Be Linearly Isomorphic](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Lipschitz-Equivalent-Separable-Banach-Spaces-Need-Not-Be-Linearly-Isomorphic-September-24-2026/paper.pdf) -- formalized: `LipschitzEquivalence`, `C0Absorption`
- [Bi-Lipschitz Absorption of c0 Without a Linear Copy of c0](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Bi-Lipschitz-Absorption-of-c0-Without-a-Linear-Copy-of-c0-September-26-2026/paper.pdf) -- formalized: `LipschitzEquivalence`, `C0Absorption`
## 325. The complete Crouzeix conjecture

Resolves the complete Crouzeix conjecture: for every bounded operator A on a complex Hilbert space and every finite matrix-valued polynomial P, one has $`\lVert P[A]\rVert\le2\sup_{z\in W(A)}\lVert P(z)\rVert`$, where $`W(A)`$ is the numerical range. The constant 2 is sharp, independent of the matrix size, and valid in infinite dimensions. ([Lean](lean/docs/325.md))

- [A direct proof of the complete Crouzeix inequality](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/paper.pdf) -- formalized: `DirectCrouzeix`, `CompleteCrouzeix`, `StructuralCrouzeix`, `CrouzeixHilbert`, `HilbertCrouzeix`
- [The complete Crouzeix theorem: optimal similarity and a common positive boundary representation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf) -- formalized: `DirectCrouzeix`, `CompleteCrouzeix`, `StructuralCrouzeix`, `CrouzeixHilbert`, `HilbertCrouzeix`
## 326. The cotype–cotype conjecture under the approximation property

Resolves the cotype–cotype conjecture for real Banach spaces with the approximation property. Such a nonzero space is K-convex if and only if both it and its dual have finite Rademacher cotype, with possibly different exponents. Equivalently, these cotype assumptions force nontrivial Rademacher type. ([Lean](lean/docs/326.md))

- [The cotype–cotype conjecture under the approximation property](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-cotype-cotype-conjecture-under-the-approximation-property-September-23-2026/paper.pdf) -- formalized: `Cotype`
## 327. Markov type characterizes superreflexivity

Proves that every real Banach space with Markov type p for some p &gt; 1 admits an equivalent uniformly convex norm, answering Naor's renorming question. Together with the known converse, this characterizes superreflexivity by nontrivial Markov type. ([Lean](lean/docs/327.md))

- [Nontrivial Markov Type Forces Superreflexivity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Nontrivial-Markov-Type-Forces-Superreflexivity-September-23-2026/paper.pdf) -- formalized: `MarkovType`
## 328. Nonexpansive fixed points in reflexive Banach spaces

Resolves Kirk's reflexive-space fixed-point problem: every nonexpansive selfmap of a nonempty closed bounded convex subset of a real reflexive Banach space has a fixed point. The result uses the original norm, without assuming uniform convexity. ([Lean](lean/docs/328.md))

- [Fixed Points of Nonexpansive Maps in Reflexive Banach Spaces](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Fixed-Points-of-Nonexpansive-Maps-in-Reflexive-Banach-Spaces-September-24-2026/paper.pdf) -- formalized: `ReflexiveFixedPoints`
## 329. A counterexample to metric-entropy duality

Disproves Pietsch's dimension-free duality conjecture for metric entropy. Origin-symmetric convex bodies violate every proposed choice of universal constants in the conjectured comparison between covering numbers and those of the polar bodies, even when the covering body is a cube. ([Lean](lean/docs/329.md))

- [Counterexamples to the duality conjecture for metric entropy](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Counterexamples-to-the-duality-conjecture-for-metric-entropy-September-24-2026/main.pdf) -- formalized: `MetricEntropyDuality`
## 330. A uniformly discrete counterexample to bounded approximation in Lipschitz-free spaces

Constructs a countable uniformly discrete metric space whose real Lipschitz-free Banach space has the approximation property but not the bounded approximation property, answering Kalton's question negatively. Finite-rank operators approximate the identity on every compact set, but their norms cannot share a finite bound. ([Lean](lean/docs/330.md))

- [A uniformly discrete counterexample to bounded approximation in Lipschitz-free spaces](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Failure-of-Bounded-Approximation-in-a-Lipschitz-Free-Space-over-a-Uniformly-Discrete-Metric-Space-September-26-2026/main.pdf) -- formalized: `RealL1Renorming`, `DiscreteLipschitzFree`
## 331. Reflexive midpoint convexity and diamond distortion

Constructs a real reflexive Banach space with an asymptotically midpoint uniformly convex norm but no equivalent asymptotically uniformly convex norm, extending Baudier's separation to reflexive spaces. In the same space, depth-k countably branching diamonds require distortion at least $`\sqrt{1+k/12}`$, so midpoint uniform convexity does not force uniformly bounded diamond distortion even under reflexivity. ([Lean](lean/docs/331.md))

- [Asymptotic midpoint uniform convexity and unbounded diamond distortion in a reflexive tree space](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Asymptotic-midpoint-uniform-convexity-and-unbounded-diamond-distortion-in-a-reflexive-tree-space-September-27-2026/manuscript.pdf) -- formalized: `ForestSpace`, `MidpointLenses`, `DiamondDistortion`, `DaugavetModuli`, `BoundedTreePotentials`, `IndependentProducts`, `RecursivePotentials`
- [Midpoint lenses in segment spaces](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Midpoint-lenses-in-segment-spaces-September-27-2026/manuscript.pdf) -- formalized: `ForestSpace`, `MidpointLenses`, `DiamondDistortion`, `DaugavetModuli`, `BoundedTreePotentials`, `IndependentProducts`, `RecursivePotentials`
- [Distortion of countably branching diamonds from midpoint and tree energies](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Diamond-distortion-from-midpoint-and-tree-energies-September-27-2026/manuscript.pdf) -- formalized: `ForestSpace`, `MidpointLenses`, `DiamondDistortion`, `DaugavetModuli`, `BoundedTreePotentials`, `IndependentProducts`, `RecursivePotentials`
- [Exact asymptotic moduli in a Daugavet subspace of L1](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-asymptotic-moduli-in-a-Daugavet-subspace-of-L1-September-27-2026/manuscript.pdf) -- formalized: `ForestSpace`, `MidpointLenses`, `DiamondDistortion`, `DaugavetModuli`, `BoundedTreePotentials`, `IndependentProducts`, `RecursivePotentials`
- [Midpoint convexity from bounded tree potentials and path costs](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Midpoint-convexity-from-bounded-tree-potentials-and-path-costs-September-27-2026/manuscript.pdf) -- formalized: `ForestSpace`, `MidpointLenses`, `DiamondDistortion`, `DaugavetModuli`, `BoundedTreePotentials`, `IndependentProducts`, `RecursivePotentials`
- [Independent products in real L1: asymptotic midpoint convexity without AUC renormings](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Independent-products-in-real-L1-asymptotic-midpoint-convexity-without-AUC-renormings-September-27-2026/manuscript.pdf) -- formalized: `ForestSpace`, `MidpointLenses`, `DiamondDistortion`, `DaugavetModuli`, `BoundedTreePotentials`, `IndependentProducts`, `RecursivePotentials`
- [Midpoint convexity from two recursive potentials](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Midpoint-convexity-from-two-recursive-potentials-September-27-2026/manuscript.pdf) -- formalized: `ForestSpace`, `MidpointLenses`, `DiamondDistortion`, `DaugavetModuli`, `BoundedTreePotentials`, `IndependentProducts`, `RecursivePotentials`
## 332. Metric Markov cotype of <i>ℓ</i><sub>1</sub> and Hilbert-space Lipschitz extension

Proves that real ℓ1 has metric Markov cotype two, answering Mendel and Naor's question. Consequently, every Lipschitz map from an arbitrary subset of a real Hilbert space into ℓ1 extends to the whole space with a universal multiplicative loss in its Lipschitz constant, resolving Ball's extension problem for this target.

- [Metric Markov Cotype Two of <i>ℓ</i><sub>1</sub> ](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Metric-Markov-Cotype-Two-of-l1-October-5-2026/l1-markov-cotype.pdf) -- no Lean statement
## 333. Smooth isometric immersions of surfaces into ℝ<sup>4</sup>

Every closed smooth Riemannian surface admits a smooth isometric immersion into ℝ4, resolving the closed-surface form of the four-dimensional isometric-immersion problem. This includes nonorientable surfaces and metrics of arbitrary Gaussian curvature. ([Lean](lean/docs/333.md))

- [Smooth isometric immersions of closed surfaces into Euclidean four-space](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Smooth-isometric-immersions-of-closed-surfaces-into-Euclidean-four-space-September-23-2026/paper.pdf) -- formalized: `SurfaceImmersion`
## 334. A smooth surface metric with no local isometric immersion in ℝ<sup>3</sup>

Constructs a smooth positive-definite metric on $`(-1,1)^2`$ for which no neighborhood of the origin admits a smooth isometric immersion into ℝ3. This answers the unrestricted smooth local isometric realization problem for surfaces negatively, even after shrinking the neighborhood. ([Lean](lean/docs/334.md))

- [A Smooth Metric with No Local Isometric Immersion into Three-Space](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf) -- formalized: `IsometricImmersion`
## 335. Gromov’s integral scalar-curvature bound for simplicial volume

Proves $`\int_M(\mathrm{Scal}_g^-)^{n/2}\,dV_g\ge a_n\lVert M\rVert`$ for every closed connected oriented smooth n-manifold, n ≥ 3, and every smooth metric, with $`a_n\gt 0`$ depending only on dimension. Here $`\mathrm{Scal}_g^-=\max\{0,-\mathrm{Scal}_g\}`$ and $`\lVert M\rVert`$ is real simplicial volume. Also proves rational inessentiality under positive scalar curvature, resolving the Gromov–Lawson conjecture; every nonnegative-scalar-curvature metric on a closed aspherical manifold is flat.

- [An integral scalar curvature bound for real simplicial volume](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-integral-scalar-curvature-bound-for-real-simplicial-volume-October-5-2026/v126-proof.pdf) -- no Lean statement
- [Positive scalar curvature forces rational inessentiality](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Positive-scalar-curvature-forces-rational-inessentiality-September-23-2026/paper.pdf) -- no Lean statement
## 336. Spectral scalar curvature, Urysohn width, and macroscopic dimension

Every complete connected smooth boundaryless n-manifold, n ≥ 3, satisfying $`-4\Delta+\mathrm{Scal}\ge1`$ as a quadratic-form inequality admits a continuous map to a simplicial complex of dimension at most $`n-2`$ whose entire fibers have diameter bounded only by n in the original metric. This strengthens Gromov's width conclusion to spectral scalar curvature. Universal covers of closed positive-scalar-curvature manifolds also have continuous macroscopic dimension at most $`n-2`$ for every n ≥ 2.

- [Spectral scalar curvature and uniform Urysohn width](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Spectral-scalar-curvature-and-uniform-Urysohn-width-October-5-2026/main.pdf) -- no Lean statement
- [Spectral scalar curvature and Urysohn width in dimension three](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Spectral-scalar-curvature-and-Urysohn-width-in-dimension-three-October-5-2026/spectral-urysohn-three-manifolds.pdf) -- no Lean statement
- [Positive scalar curvature and uniform codimension-two width](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Positive-scalar-curvature-and-uniform-codimension-two-width-September-23-2026/paper.pdf) -- no Lean statement
## 337. Sharp Cartan–Hadamard isoperimetry and rigidity

Proves generalized Cartan–Hadamard isoperimetry in every dimension: in a complete simply connected manifold with sectional curvature at most κ ≤ 0, every finite-volume finite-perimeter set satisfies the sharp comparison with the equal-volume model ball. Bounded positive-volume equality regions for κ = 0 are Euclidean balls. Also proves sharp Euclidean filling bounds for compactly supported integral n-cycles, n ≥ 2, in arbitrary proper CAT$`(0)`$ spaces. ([Lean](lean/docs/337.md))

- [Generalized Cartan–Hadamard isoperimetry and Euclidean equality rigidity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Generalized-Cartan-Hadamard-isoperimetry-and-Euclidean-equality-rigidity-September-23-2026/paper.pdf) -- no Lean statement
- [Sharp integral fillings in CAT(0) spaces](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf) -- no Lean statement
## 338. Yau's uniformization conjecture

Proves Yau's uniformization conjecture: every complete connected noncompact Kähler manifold with strictly positive holomorphic bisectional curvature is biholomorphic to ℂn.

- [Uniformization of complete Kähler manifolds with positive bisectional curvature](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniformization-of-complete-Kahler-manifolds-with-positive-bisectional-curvature-September-23-2026/paper.pdf) -- no Lean statement
## 339. Katok's entropy rigidity conjecture

Proves Katok's entropy rigidity conjecture for closed connected Riemannian manifolds of dimension at least three with strictly negative sectional curvature: normalized Liouville measure maximizes entropy for the geodesic flow if and only if the metric is locally symmetric.

- [Entropy equality and local symmetry in negative curvature](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Entropy-equality-and-local-symmetry-in-negative-curvature-September-23-2026/paper.pdf) -- no Lean statement
## 340. A counterexample to the nearby Lagrangian conjecture

Disproves the unrestricted nearby Lagrangian conjecture. For some sufficiently large even N, constructs a closed exact embedded Lagrangian in $`T^*(S^9\times S^{N-1})`$ that is diffeomorphic to the base but not Hamiltonian isotopic to its zero section.

- [A counterexample to the nearby Lagrangian conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-the-nearby-Lagrangian-conjecture-September-23-2026/paper.pdf) -- no Lean statement
## 341. Donaldson's hypersymplectic deformation conjecture

Proves Donaldson's hypersymplectic deformation conjecture in a cohomology-preserving form. Every positive triple of smooth closed two-forms on a closed connected oriented four-manifold, normalized by $`\int\omega_i\wedge\omega_j=\delta_{ij}`$, deforms through positive closed triples to a hyperkähler triple while preserving all three cohomology classes. Any positive triple can first be normalized by a constant linear change.

- [Deforming hypersymplectic four-manifolds to hyperkähler triples](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Deforming-hypersymplectic-four-manifolds-to-hyperkahler-triples-October-7-2026/paper.pdf) -- no Lean statement
## 342. Donaldson's tamed-to-compatible conjecture

Proves Donaldson's tamed-to-compatible conjecture: every smooth almost complex structure on a closed four-manifold that is tamed by a symplectic form admits a compatible symplectic form. The almost complex structure stays fixed; the form's cohomology class may change. ([Lean](lean/docs/342.md))

- [Taming implies compatibility on four-manifolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf) -- no Lean statement
## 343. Symplectic ball packing in higher dimensions

Resolves the Siegel–Yao conjecture for arbitrary capacities in every dimension $`2n\ge6`$. Finitely many closed symplectic balls of capacities $`R_1,\ldots,R_k`$ embed disjointly into an open ball of capacity R exactly when $`\sum_iR_i^n\lt R^n`$ and $`R_i+R_j\lt R`$ for every distinct pair i, j. ([Lean](lean/docs/343.md))

- [Symplectic Ball Packings in Higher Dimensions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf) -- formalized: `BallPacking`, `BallPackingNecessity`
## 344. The metric Blaschke conjecture

Proves the metric Blaschke conjecture: every closed connected Riemannian manifold of positive dimension whose injectivity radius equals its diameter is, up to scaling, a standard compact rank-one symmetric space.

- [The metric Blaschke theorem](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-metric-Blaschke-theorem-September-23-2026/paper.pdf) -- no Lean statement
## 345. Infinitely many closed geodesics on Riemannian spheres and closed three-manifolds

Proves that every smooth Riemannian metric on Sn, n ≥ 2, has infinitely many prime closed geodesics with pairwise distinct images. The same conclusion holds on every closed manifold admitting a finite smooth spherical cover and on every closed three-manifold, without orientability or nondegeneracy restrictions.

- [Infinitely many closed geodesic images on every Riemannian sphere](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Infinitely-many-closed-geodesic-images-on-every-Riemannian-sphere-September-24-2026/paper.pdf) -- no Lean statement
## 346. Sharp singular-set bounds for stationary integral varifolds

Proves that every stationary integral m-varifold in a Euclidean open set has singular set of Hausdorff dimension at most $`m-1`$, a sharp bound in every positive dimension and codimension. On round spheres, the family also proves almost-everywhere regularity: the singular set has zero m-dimensional Hausdorff measure.

- [A Codimension-One Bound for the Singular Set of a Stationary Integral Varifold](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Codimension-One-Bound-for-the-Singular-Set-of-a-Stationary-Integral-Varifold-October-5-2026/varifold-singular-dimension.pdf) -- no Lean statement
- [Almost-everywhere regularity of stationary integral varifolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Almost-everywhere-regularity-of-stationary-integral-varifolds-September-23-2026/paper.pdf) -- no Lean statement
## 347. Counterexamples to stable-Morse and strong Arnold fixed-point bounds

Disproves stable-Morse lower bounds for nondegenerate Hamiltonian fixed points: on simply connected closed Kähler manifolds of real dimension 22, the deficit below the stable Morse number is unbounded. A separate Hamiltonian diffeomorphism of the complex quadric threefold has exactly three fixed points, fewer than the four critical points required of every smooth function. ([Lean](lean/docs/347.md))

- [Hamiltonian Fixed Points Below the Stable Morse Number in Dimension Twenty-Two](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hamiltonian-Fixed-Points-Below-the-Stable-Morse-Number-in-Dimension-Twenty-Two-October-5-2026/hamiltonian-fixed-points-below-stable-morse-number.pdf) -- no Lean statement
- [Sharpness of the Cyclic Integral Floer Bound Below the Stable Morse Number](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharpness-of-the-Cyclic-Integral-Floer-Bound-Below-the-Stable-Morse-Number-October-5-2026/sharp-cyclic-integral-floer-bound-below-stable-morse-number.pdf) -- no Lean statement
- [Hamiltonian Fixed Points Below the Stable Morse Number](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hamiltonian-Fixed-Points-Below-the-Stable-Morse-Number-October-5-2026/paper.pdf) -- no Lean statement
- [A nondegenerate counterexample to the Morse-number Arnold bound](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-nondegenerate-counterexample-to-the-Morse-number-Arnold-bound-September-23-2026/paper.pdf) -- no Lean statement
- [Three fixed points on the symplectic quadric threefold](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-degenerate-counterexample-to-the-critical-number-Arnold-bound-September-23-2026/paper.pdf) -- formalized: `ArnoldCounterexample`
## 348. Nonnegative-curvature Einstein classification and an <i>L</i><sup>2</sup> topological gap

Classifies closed connected Einstein four-manifolds with positive Einstein constant and nonnegative sectional curvature: up to scaling, their universal Riemannian covers are the round S4, Fubini–Study $`\mathbb{CP}^2`$, or a product of equal round two-spheres. A closed simply connected nonnegatively curved four-manifold is diffeomorphic to one of these whenever the scale-invariant L2 norm of its trace-free Ricci curvature lies below a universal positive constant. ([Lean](lean/docs/348.md))

- [Zero-Plane Rigidity for Einstein Four-Manifolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Zero-Plane-Rigidity-for-Einstein-Four-Manifolds-October-4-2026/einstein-boundary.pdf) -- no Lean statement
- [An L² Einstein Gap for Nonnegatively Curved Four-Manifolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-L2-Einstein-Gap-for-Nonnegatively-Curved-Four-Manifolds-October-5-2026/einstein-gap.pdf) -- no Lean statement
- [Positively curved Einstein four-manifolds](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf) -- formalized: `EinsteinFour`
## 349. The Solomon–Yau least-volume conjecture

Proves the Solomon–Yau least-volume conjecture for minimal hypersurfaces of round spheres. For every m ≥ 2, a closed connected minimal immersion into the unit sphere $`S^{m+1}`$ with non-totally-geodesic image has volume at least that of the smallest minimal Clifford product, counting covering multiplicity.

- [The Solomon–Yau least-volume theorem](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Solomon-Yau-least-volume-theorem-September-23-2026/paper.pdf) -- no Lean statement
## 350. Yau’s nodal bounds: surfaces and higher dimensions

Proves the sharp $`C\sqrt\lambda`$ upper bound for nodal length on every fixed smooth closed surface, completing Yau's conjecture there. The upper bound fails for fixed smooth metrics in dimensions three and four, including metrics on S3 arbitrarily close to round. In dimension five, nodal measure can grow faster than $`\lambda^{1/2+\varepsilon_0}`$ for some fixed $`\varepsilon_0\gt 0`$, ruling out even arbitrarily small power losses. ([Lean](lean/docs/350.md))

- [Sharp nodal length on smooth surfaces](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-nodal-length-on-smooth-surfaces-September-23-2026/paper.pdf) -- formalized: `NodalLength`, `SmoothYau`, `YauCounterexample`
- [Smooth counterexamples to Yau's nodal upper bound in dimensions three and four](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf) -- formalized: `NodalLength`, `SmoothYau`, `YauCounterexample`
- [Power-law violations of Yau's nodal upper bound](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf) -- formalized: `NodalLength`, `SmoothYau`, `YauCounterexample`
## 351. Scalar curvature and finite-time Ricci-flow singularities

Proves that a smooth Ricci flow on a closed four-manifold extends past any finite time at which scalar curvature remains uniformly bounded. A higher-dimensional counterexample has bounded scalar curvature but unbounded full curvature at its finite maximal time, disproving the unrestricted scalar-curvature extension conjecture.

- [A closed Ricci flow with bounded scalar curvature and finite-time curvature blowup](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-closed-Ricci-flow-with-bounded-scalar-curvature-and-finite-time-curvature-blowup-September-24-2026/paper.pdf) -- no Lean statement
- [Bounded scalar curvature and smooth extension of four-dimensional Ricci flow](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Bounded-scalar-curvature-and-smooth-extension-of-four-dimensional-Ricci-flow-September-24-2026/paper.pdf) -- no Lean statement
- [Path selection and an elliptic inequality on degenerating Ricci-flat trees](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Path-selection-and-an-elliptic-inequality-on-degenerating-Ricci-flat-trees-September-24-2026/paper.pdf) -- no Lean statement
## 352. A finite-time singularity of Calabi flow

Disproves Chen's smooth long-time existence conjecture for Calabi flow by constructing a smooth $`U(10)`$-invariant Kähler metric on $`\mathbb{CP}^{10}`$ whose flow develops a finite-time singularity. The metric lies in the Fubini–Study class, so the failure occurs even in a class containing a constant-scalar-curvature metric.

- [A finite-time singularity of Calabi flow on projective space](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-finite-time-singularity-of-Calabi-flow-on-projective-space-September-24-2026/paper.pdf) -- no Lean statement
## 353. Affine Bernstein rigidity through dimension nine and a smooth dimension-ten counterexample

Proves that every smooth locally uniformly convex affine-maximal graph of dimension three through nine, complete for its induced Euclidean metric, is an elliptic paraboloid. A smooth entire nonquadratic example in dimension ten makes this range sharp. In dimensions three through nine, the paraboloid classification also holds for connected open locally uniformly convex affine-maximal hypersurfaces complete for the affine Berwald–Blaschke metric. ([Lean](lean/docs/353.md))

- [A Smooth Nonquadratic Entire Affine Maximal Graph in Dimension Ten](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Smooth-Nonquadratic-Affine-Maximal-Graph-in-Dimension-Ten-October-5-2026/affine-maximal-dimension-ten.pdf) -- no Lean statement
- [The affine Bernstein theorem in dimensions three through nine](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf) -- formalized: `AffineBernstein`
## 354. The isoperimetric profile of the cubic three-torus

Determines the isoperimetric profile of the unit cubic flat three-torus and classifies every finite-perimeter minimizer: balls, circular tubes around shortest closed geodesics, coordinate slabs, and their complements. The transition volumes are $`4\pi/81`$ and $`1/\pi`$, with exactly the adjacent two types minimizing at each transition. ([Lean](lean/docs/354.md))

- [The Isoperimetric Conjecture for the Cubic Flat Three-Torus](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf) -- formalized: `CubicTorus`
## 355. Unique tangent flows at the first surface singularity

Proves the first-singular-time case of tangent-flow uniqueness for smooth compact connected embedded surfaces without boundary in ℝ3. At every singular point, all fixed-center backward tangent flows agree as area measures at every negative time in the original ambient coordinates, without mean-convexity or a prescribed tangent model.

- [Uniqueness of tangent flows at the first singular time of embedded surface mean-curvature flow](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Tangent-flow-uniqueness-2026-09-24/paper.pdf) -- no Lean statement
## 356. Gigli’s characterization of Alexandrov curvature

Proves Gigli's conjecture: in every integer dimension n ≥ 2, Alexandrov curvature at least κ is characterized by the full-support $`\mathop{\mathrm{RCD}}\nolimits ((n-1)\kappa,n)`$ condition with reference measure $`\mathcal H^n`$ and distributional sectional curvature at least κ in the original global test classes. The RCD condition is unreduced. ([Lean](lean/docs/356.md))

- [Gigli’s distributional curvature characterization of Alexandrov spaces](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Giglis-distributional-curvature-characterization-of-Alexandrov-spaces-September-24-2026/main.pdf) -- no Lean statement
- [Weak Hessian bounds along every geodesic in RCD spaces](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf) -- formalized: `WeakHessian`
## 357. Bi-Lipschitz coordinates at every regular RCD point

Proves that every regular point of a noncollapsed $`\mathop{\mathrm{RCD}}\nolimits (K,n)`$ space, for K ∈ ℝ and integer n ≥ 2, has an open neighborhood bi-Lipschitz to an open subset of ℝn. Regularity requires all pointed tangents to be Euclidean, the reference measure is exactly $`\mathcal H^n`$, and the chart compares ambient distances with a point-dependent finite constant.

- [Bi-Lipschitz Coordinates at Regular Points of Noncollapsed RCD Spaces](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Bi-Lipschitz-Coordinates-at-Regular-Points-of-Noncollapsed-RCD-Spaces-September-25-2026/paper.pdf) -- no Lean statement
## 358. A three-manifold without conjugate points or nonpositive curvature

Constructs a closed connected orientable smooth three-manifold that admits a metric without conjugate points but no metric of nonpositive sectional curvature. This answers negatively, already in dimension three, whether the first metric-existence property implies the second. ([Lean](lean/docs/358.md))

- [A Three-Manifold Without Conjugate Points and Without a Nonpositively Curved Metric](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Three-Manifold-Without-Conjugate-Points-and-Without-a-Nonpositively-Curved-Metric-September-24-2026/paper.pdf) -- formalized: `ConjugatePoints`
## 359. Negative Kähler curvature without bounded holomorphic coordinates

Constructs a contractible domain in ℂ3 with a complete negatively pinched Kähler metric but no bounded holomorphic coordinates, disproving bounded-domain uniformization in this setting. A higher-dimensional example has sectional curvature at most −1 and only constant bounded holomorphic functions; its curvature is not bounded below. ([Lean](lean/docs/359.md))

- [A negatively pinched Kähler threefold without bounded holomorphic coordinates](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-negatively-pinched-Kahler-threefold-without-bounded-holomorphic-coordinates-September-25-2026/paper.pdf) -- formalized: `PinchedKahler`
- [One-sided negative sectional curvature and the holomorphic Liouville property](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/One-sided-negative-sectional-curvature-and-the-holomorphic-Liouville-property-September-25-2026/paper.pdf) -- no Lean statement
## 360. Weak MTW curvature gives convexity and regular optimal transport

On every closed connected Riemannian manifold of dimension at least two satisfying weak Ma–Trudinger–Wang curvature, all tangent injectivity domains are convex, resolving Villani’s conjecture in this setting. For squared-distance transport between measurable probability densities bounded above and away from zero, the optimal map and its inverse are Hölder continuous. ([Lean](lean/docs/360.md))

- [Global Support and Convex Injectivity Domains under Weak MTW](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf) -- formalized: `WeakMTWGlobalSupport`, `BiholderTransport`
- [Uniform Bi-Holder Transport from Weak MTW](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf) -- formalized: `WeakMTWGlobalSupport`, `BiholderTransport`
## 361. Failure of integer-degree harmonic dimension comparison

Disproves Yau's proposed Euclidean dimension bound for harmonic functions of integer growth on manifolds with nonnegative Ricci curvature. For every sufficiently large integer k, a complete smooth metric on ℝ3 has at least $`(k+2)^2`$ independent harmonic functions of growth at most k, exceeding the Euclidean count $`(k+1)^2`$. The metric may depend on k. ([Lean](lean/docs/361.md))

- [A counterexample to integer-degree harmonic dimension comparison](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-integer-degree-harmonic-dimension-comparison-September-25-2026/paper.pdf) -- formalized: `HarmonicGrowth`
- [A Three-Dimensional Counterexample to Integer-Degree Harmonic Dimension Comparison](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Three-Dimensional-Counterexample-to-Integer-Degree-Harmonic-Dimension-Comparison-September-26-2026/paper.pdf) -- no Lean statement
## 362. Global smoothness for relativistic Vlasov–Maxwell

Proves large-data global existence and uniqueness for the three-dimensional, one-species relativistic Vlasov–Maxwell system. Smooth admissible initial data may be arbitrary provided the particle density is compactly supported and the electromagnetic fields have finite energy and bounded derivatives of every order; the solution remains smooth on every finite time interval. ([Lean](lean/docs/362.md))

- [Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf) -- formalized: `VlasovMaxwell`
## 363. Nonuniqueness with local conservation for the hard-sphere Boltzmann equation

Constructs two distinct global entropy solutions of the three-dimensional periodic hard-sphere Boltzmann equation from the same nonnegative initial density, with bounded velocity support and finite mass, energy and absolute entropy. Both are strongly continuous in L1 and satisfy exact local conservation of mass, momentum and kinetic energy. ([Lean](lean/docs/363.md))

- [Nonuniqueness with local conservation for the hard-sphere Boltzmann equation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Nonuniqueness-with-local-conservation-for-the-hard-sphere-Boltzmann-equation-October-5-2026/paper.pdf) -- no Lean statement
- [Nonuniqueness for the periodic hard-sphere Boltzmann equation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf) -- formalized: `BoltzmannNonuniqueness`
## 364. Kinetic limits and fluctuations over the Boltzmann lifespan

Derives the nonlinear Boltzmann equation from three-dimensional grand-canonical Newtonian gases throughout every regular kinetic interval with uniform Gaussian decay. Stable finite-range radial potentials may have attractive wells and a singular repulsive core; initial pair exclusion and spatially summable Gaussian density and gradient bounds are assumed. A companion gives finite-dimensional hard-sphere Gaussian fluctuations, centered at the exact microscopic expectation and governed by the linear fluctuating Boltzmann equation.

- [The Boltzmann–Grad limit for stable radial potentials on regular kinetic intervals](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Boltzmann-Grad-limit-for-stable-radial-potentials-on-regular-kinetic-intervals-September-23-2026/paper.pdf) -- no Lean statement
- [Hard-sphere fluctuations on the regular Boltzmann lifespan](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/paper.pdf) -- no Lean statement
## 365. Joint metric and connection recovery from one boundary patch

Zero-frequency measurements on any nonempty open boundary patch determine a smooth metric and smooth unitary connection on a trivial Hermitian rank-two bundle over a compact connected manifold of dimension at least three, up to diffeomorphism and gauge fixed on that patch. Inputs and observations use the same patch. In contrast, distinct uniformly positive bounded measurable scalar conductivities on a three-dimensional ball can have identical full-boundary data. ([Lean](lean/docs/365.md))

- [Determination of a metric and a unitary connection from one boundary patch](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Determination-of-a-metric-and-a-unitary-connection-from-one-boundary-patch-October-5-2026/paper.pdf) -- no Lean statement
- [Smooth anisotropic uniqueness in the Calderón problem from one boundary patch](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026/paper.pdf) -- no Lean statement
- [Nonuniqueness for bounded measurable scalar conductivities in three dimensions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf) -- formalized: `Conductivity`
## 366. The planar Mumford–Shah regularity conjecture and local weak-<i>L</i><sup>4</sup> gradient bounds

Resolves the interior regularity conjecture for reduced absolute planar Mumford–Shah minimizers with bounded fidelity data. Locally, the closed discontinuity set is a $`C^{1,\alpha}`$ arc, a regular crack tip, or three arcs meeting at $`120^\circ`$; only finitely many global connected components meet any compact interior region.

- [Interior regularity of planar Mumford–Shah minimizers](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Interior-regularity-of-planar-Mumford-Shah-minimizers-September-24-2026/Interior-regularity-of-planar-Mumford-Shah-minimizers-September-24-2026.pdf) -- no Lean statement
## 367. The critical dimension for the one-phase Bernoulli problem

Establishes seven as the first dimension admitting a nonflat, one-homogeneous global minimizer of the one-phase Bernoulli energy. Consequently, minimizing free boundaries are smooth through dimension six, and their singular sets have dimension at most $`n-7`$ in higher dimensions. ([Lean](lean/docs/367.md))

- [The critical dimension for one-phase Bernoulli minimizers](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026.pdf) -- formalized: `BernoulliNonflatInSeven`
## 368. The three-dimensional Ball–Evans approximation problem

Resolves the three-dimensional Ball–Evans approximation problem: every $`W^{1,p}`$ homeomorphism between arbitrary bounded domains in ℝ3, for $`1\le p\lt \infty`$, is a strong $`W^{1,p}`$ limit of smooth diffeomorphisms onto the same target.

- [Strong diffeomorphic approximation in three dimensions for 1≤p≤2](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Strong-diffeomorphic-approximation-in-three-dimensions-for-1-le-p-le-2-September-24-2026/main.pdf) -- no Lean statement
- [Strong diffeomorphic approximation in three dimensions for p>2](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Strong-diffeomorphic-approximation-in-three-dimensions-for-p-gt-2-September-24-2026/main.pdf) -- no Lean statement
## 369. The hot spots conjecture for simply connected planar domains

Proves a strict form of Burdzy's simply connected hot spots conjecture. On every smooth bounded simply connected planar domain, each nonzero eigenfunction for the first positive Neumann eigenvalue has no interior critical point, so all global extrema lie on the boundary. Eigenvalue multiplicity is allowed. ([Lean](lean/docs/369.md))

- [Strict hot spots and absence of interior critical points on smooth simply connected planar domains](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf) -- formalized: `HotSpots`
## 370. The Lane–Emden and Hénon–Lane–Emden conjectures

Resolves the subcritical Lane–Emden conjecture and its weighted Hénon extension. For n ≥ 2, $`p,q\gt 0`$ and real A, B, the system $`-\Delta u=|x|^A v^p`$, $`-\Delta v=|x|^B u^q`$ has no positive entire solution when $`(n+A)/(p+1)+(n+B)/(q+1)\gt n-2`$, with solutions continuous at the origin and classical elsewhere. No symmetry or growth assumption is needed. Known radial existence gives the exact existence criterion for n ≥ 3 and $`A,B\gt -2`$. ([Lean](lean/docs/370.md))

- [The Subcritical Hénon–Lane–Emden Conjecture](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Subcritical-Henon-Lane-Emden-Conjecture-September-24-2026/paper.pdf) -- formalized: `HenonEmden`
## 371. Stable blowup for the defocusing Schrödinger equation

For a sufficiently large odd nonlinearity power, constructs a nonempty open set of initial data in $`H^k(\mathbb T^{12})`$, with k &gt; 8, whose solutions of the scalar defocusing nonlinear Schrödinger equation blow up in finite time. Thus finite-time blowup is stable under Sobolev perturbations in this supercritical regime. ([Lean](lean/docs/371.md))

- [Stable self-similar blowup for a supercritical defocusing Schrödinger equation on the torus](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Stable-Self-Similar-Blowup-for-a-Supercritical-Defocusing-Schrodinger-Equation-on-the-Torus-September-24-2026/paper.pdf) -- formalized: `DefocusingNLS`
## 372. Global uniqueness in smooth isotropic elasticity

Proves that full static boundary displacement-to-traction data determine both smooth real Lamé moduli on every bounded connected smooth domain in ℝ3, provided μ &gt; 0 and $`3\lambda+2\mu\gt 0`$ on the closure. Neither analyticity, proximity to constant coefficients nor prior knowledge near the boundary is required. ([Lean](lean/docs/372.md))

- [Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf) -- formalized: `ElasticityUniqueness`
## 373. Nonattainment of the three-marginal Coulomb Monge problem

An optimal three-particle Coulomb configuration need not be a deterministic function of the first particle, even for smooth identical spatial densities. The Monge and Kantorovich infima agree, but the Monge infimum is not attained. The same phenomenon occurs for every inverse-power Riesz exponent in each dimension at least two, with a suitable density in each case. ([Lean](lean/docs/373.md))

- [A counterexample to the Monge ansatz for the three-marginal Coulomb cost](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-the-Monge-ansatz-for-the-three-marginal-Coulomb-cost-September-25-2026/paper.pdf) -- formalized: `CoulombCounterexample`
## 374. Sharp one-third stability of Brenier maps

For uniform source measure ρ on a compact convex body with interior in dimension at least two, quadratic optimal transport maps satisfy $`\|T_\mu-T_\nu\|_{L^2(\rho)}\le C W_2(\mu,\nu)^{1/3}`$ uniformly over targets in a fixed compact set. The exponent is sharp, even for three-atom targets, disproving Letrouit's conjectured square-root bound. ([Lean](lean/docs/374.md))

- [Sharp One-Third Stability of Brenier Maps](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/article.pdf) -- formalized: `Brenier`
## 375. De Giorgi's conjecture in dimension eight

Proves De Giorgi's conjecture at its sharp dimension-eight endpoint: every entire C2 solution $`u:\mathbb R^8\to(-1,1)`$ of $`\Delta u=u^3-u`$ that is strictly increasing in one direction depends on only one linear coordinate. A stronger theorem classifies all stable entire solutions $`v:\mathbb R^7\to[-1,1]`$ as constant wells or planar transitions, without an energy-growth assumption.

- [A positive resolution of De Giorgi's conjecture in dimension eight](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/De-Giorgis-conjecture-in-dimension-eight-September-26-2026/article.pdf) -- no Lean statement
## 376. Universal computation in forced Navier–Stokes flows

Constructs viscous incompressible flows starting from rest on a fixed flat three-dimensional domain that perform universal computation under smooth external forcing. A terminating compiler turns a Turing machine and input into a finite program for the force, so a designated particle reaches a fixed region exactly when the machine halts. The viscosity is fixed, positive and computable. ([Lean](lean/docs/376.md))

- [Finite Instructions and Solenoidal Shear Flows](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-Instructions-and-Solenoidal-Shear-Flows-September-27-2026/manuscript.pdf) -- no Lean statement
- [A Fixed Particle Test for Computation in a Forced Viscous Flow](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Fixed-Particle-Test-for-Computation-in-a-Forced-Viscous-Flow-September-27-2026/manuscript.pdf) -- no Lean statement
- [Universal Computation with Eventually Stationary Navier–Stokes Forcing](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Universal-Computation-with-Eventually-Stationary-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf) -- no Lean statement
- [Geometric Programs for Solenoidal Forcing](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Geometric-Programs-for-Solenoidal-Forcing-September-27-2026/manuscript.pdf) -- formalized: `SolenoidalSheetPrograms`, `NavierStokesAlternating`, `NavierStokesVelocity`, `BalancedBoxRouting`, `BalancedThreeStack`, `ForcedNavierStokesComputation`
- [Prefix Instructions and Incompressible Flows](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Prefix-Instructions-and-Incompressible-Flows-September-27-2026/manuscript.pdf) -- no Lean statement
- [Computation under Rapidly Vanishing Navier–Stokes Forcing](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf) -- formalized: `SolenoidalSheetPrograms`, `NavierStokesAlternating`, `NavierStokesVelocity`, `BalancedBoxRouting`, `BalancedThreeStack`, `ForcedNavierStokesComputation`
- [Velocity-Field Detection of Computation in Forced Navier–Stokes Flows](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Velocity-Field-Detection-of-Computation-in-Forced-Navier-Stokes-Flows-September-27-2026/manuscript.pdf) -- formalized: `SolenoidalSheetPrograms`, `NavierStokesAlternating`, `NavierStokesVelocity`, `BalancedBoxRouting`, `BalancedThreeStack`, `ForcedNavierStokesComputation`
- [Scalar Potentials and Slow Clocks for Forced Fluid Computation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Scalar-Potentials-and-Slow-Clocks-for-Forced-Fluid-Computation-September-27-2026/manuscript.pdf) -- no Lean statement
- [Incompressible Box Transport and Finite Computation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Incompressible-Box-Transport-and-Finite-Computation-October-6-2026/manuscript.pdf) -- no Lean statement
## 377. Interior $`C^{1,\alpha}`$ regularity for infinity-harmonic functions

Proves uniform interior $`C^{1,\alpha_d}`$ regularity for bounded infinity-harmonic functions in every dimension d ≥ 3, for a positive exponent depending only on dimension. The gradient's supremum norm and Hölder seminorm on the half unit ball are bounded by a dimension-dependent constant times the oscillation on the unit ball. The exponent is not explicit.

- [Uniform Interior $`C^{1,\alpha}`$ Estimates for Infinity-Harmonic Functions](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/interior-c1-infinity-harmonic.pdf) -- no Lean statement
