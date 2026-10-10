import Mathlib
/-
Copyright 2026 OpenAI. Licensed under the Apache License, Version 2.0.
Copyright 2026 The mathdb-lean Authors.

The definitions and the statements below are OpenAI's, from
github.com/openai/math at the revision named in the metadata block; see NOTICE.
What this library changed: each `sorry`-bodied theorem became the definition of
the proposition it stated, and `Problem.Target` conjoins those propositions.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
Converted from github.com/openai/math. `source_locator` names the comparator
challenge this came from and `source_solution_module` the module there that
proves it; both are at `source_version`. The definitions are the challenge's
own; each sorried theorem became `<name>_statement`, and `Problem.Target`
below conjoins them. `track` is solved because comparator accepted OpenAI's
proof against this very statement. Whether the statement says what the paper's
title says is what the scope note, carried as a caveat, is about.

- problem_id: FourRowPermanent
- collection: openai-math
- question_id: openai-math:238
- source: openai-math
- source_locator: lean/ComparatorChallenges/FourRowPermanent.lean#OAI.FourRow.robust_permanent
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that the Thorp shuffle randomizes $`N=2^d`$ labeled cards in $`\Theta(\log N)`$ physical shuffles, settling its optimal mixing order for power-of-two deck sizes. Convergence is in total variation from the worst initial ordering and concerns the entire permutation, not just individual card positions. ([Lean](lean/docs/238.md)) We prove that the Thorp shuffle on $`2^d`$ cards mixes in $`\Theta(d)`$ complete shuffles. The full permutation law after $`1600d`$ shuffles converges to uniform in total variation as $`d\to\infty`$, uniformly over the initial deck, while a support count gives a lower bound of $`2d-O(1)`$. We show how information about partial permutations controls full permutation laws. Let n tend to infinity through multiples of eight. If the images of a uniformly chosen $`7n/8`$ labels approach the uniform injection law in average total variation, and the sign mean tends to zero, then the product of two independent permutations with the given law converges to uniform on Sn. Fix half the labels in a Thorp shuffle on $`2^d`$ positions and reveal their complete trajectories. We prove that, after an explicit absolute number of coordinate sweeps, the conditional permutation of the remaining labels approaches uniform in expected total variation as $`d\to\infty`$, uniformly in the initial layout. The resulting constructions give full-deck mixing in a constant multiple of d physical shuffles. For $`N=2^d`$ cards, we prove that an absolute number of coordinate sweeps of the Thorp shuffle brings the full permutation law to total-variation distance tending to zero from uniform. The mixing time therefore has optimal order $`\Theta(\log N)`$ in physical shuffles. We prove that the Thorp shuffle on $`N=2^d`$ labeled cards has full-permutation total-variation mixing time $`\Theta(\log N)`$ in physical shuffles. An absolute number of coordinate sweeps suffices for the upper bound. We prove that an absolute number of coordinate sweeps of the Thorp shuffle on $`n=2^d`$ positions brings the full permutation to total-variation distance at most $`\frac12n^{-5}`$ from uniform, uniformly over the initial deck. Thus $`O(d)`$ physical shuffles suffice, which is optimal in order. We prove that the Thorp shuffle on $`n=2^d`$ cards mixes in $`\Theta(d)`$ physical shuffles. After a sufficiently large fixed number of coordinate sweeps, the total-variation distance of the full permutation from uniform tends to zero as $`d\to\infty`$. We prove that a fixed number of coordinate sweeps of the Thorp shuffle on $`2^d`$ cards makes the squared L2 distance of the full permutation density from uniform tend to zero as $`d\to\infty`$. In particular, the total-variation mixing time is $`\Theta(d)`$ physical shuffles. For coordinate sweeps with near-uniform line laws and line sizes among powers of two in a suitable fixed interval, we prove a Schatten-moment bound after conditioning on any feasible collection of prescribed card trajectories. An analytic transfer to binary sweeps then shows that a fixed number of sweeps mixes the Thorp shuffle on $`2^d`$ cards in $`O(d)`$ physical steps, matching the order of the support lower bound. We prove a permanent inequality with exponent strictly below two for laws on S4 sufficiently close to uniform and with exactly uniform coordinate marginals. Applied to a four-row recursion, it shows that an absolute number of coordinate sweeps brings the full permutation of the Thorp shuffle on $`N=2^d`$ cards to total-variation distance tending to zero from uniform as $`N\to\infty`$. Thus the mixing time has the optimal order $`O(\log N)`$ in physical shuffles.
- notes: OpenAI math result family 238, Optimal logarithmic mixing of the Thorp shuffle -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/238.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.FourRow.robust_permanent
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.Permanent.Main
- source_papers: preprints/Optimal-order-mixing-of-the-Thorp-shuffle-September-26-2026/paper.pdf preprints/From-partial-permutation-information-to-Fourier-bounds-September-26-2026/main.pdf preprints/Conditional-permutations-in-a-revealed-switching-environment-September-26-2026/paper.pdf preprints/Routing-densities-and-representation-contraction-for-Thorp-sweeps-September-26-2026/paper.pdf preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf preprints/Random-subspace-tests-and-trace-smoothing-for-coordinate-sweeps-September-26-2026/paper.pdf preprints/Compatibility-entropy-and-the-spectrum-of-a-Thorp-sweep-September-26-2026/paper.pdf preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf preprints/Conditional-coordinate-sweeps-and-analytic-transfer-September-26-2026/main.pdf preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026/main.pdf
- source_scope_note: lean/docs/238.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-!
# A robust four-row permanent inequality

`Fin 4` labels four sites. A law is represented by real probability masses;
`IsProbability` asserts nonnegativity and total mass one. All row norms use
the uniform counting normalization.
-/

noncomputable section
namespace FourRow
open scoped BigOperators

abbrev Site := Fin 4
abbrev Perm := Equiv.Perm Site
abbrev Law := Perm → ℝ
abbrev Functions := Site → Site → ℝ

def IsProbability (ν : Law) : Prop :=
  (∀ π, 0 ≤ ν π) ∧ ∑ π, ν π = 1

def UniformMarginals (ν : Law) : Prop :=
  ∀ i j : Site, ∑ π, (if π i = j then ν π else 0) = 1 / 4

def totalVariation (ν : Law) : ℝ :=
  (∑ π, |ν π - 1 / 24|) / 2

def lpNorm (p : ℝ) (f : Site → ℝ) : ℝ :=
  ((∑ j, (f j) ^ p) / 4) ^ (1 / p)

def permanentExpectation (ν : Law) (f : Functions) : ℝ :=
  ∑ π, ν π * ∏ i, f i (π i)

def robust_permanent_statement : Prop :=
  ∃ p₀ : ℝ, 4 / 3 < p₀ ∧ p₀ < 2 ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν : Law,
      IsProbability ν → totalVariation ν < ε → UniformMarginals ν →
      ∀ f : Functions, (∀ i j, 0 ≤ f i j) →
        permanentExpectation ν f ≤ ∏ i, lpNorm p₀ (f i)

end FourRow
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.FourRow.robust_permanent_statement

end Problem

/- Formalization scope, from lean/docs/238.md: The formalization proves optimal-order mixing of the Thorp shuffle on $2^d$ cards. After $1600d$ complete shuffles, the full permutation law converges in total variation to uniform as $d\to\infty$, uniformly over initial decks. Together with the support lower bound of $2d-O(1)$, this gives mixing time $\Theta(d)=\Theta(\log(2^d))$. The linked supporting results include frame and conditional-list estimates, regular trace and spectral bounds, signed moments, and full-density $L^2$ control. They also bound reciprocal Specht-dimension sums and give the eight-block Fourier estimate used in the mixing argument. The formalized supporting result turns bounds on partial-permutation cosets into Fourier bounds. Partition a finite set into $b\ge1$ nonempty blocks, and let $f\ge0$ be a subprobability weight on its symmetric group whose left-coset masses for each block subgroup are at most $B$. For every irreducible unitary representation of dimension $D$ and every $u>0$, both the squared Hilbert–Schmidt norm and squared operator norm of its Fourier transform are at most $bB\,C(u)D^{-1+(u+2)/b}$, where $C(u)$ is the stated symmetric-group degree constant. The paper's asymptotic conclusion about the product of two random permutations is outside this selected finite estimate. The formalized results give averaged conditional mixing for half-permutations in the revealed-path model and full-deck mixing for the Thorp shuffle. In particular, the full-deck total-variation distance tends to zero after $16040400d$ steps on $2^d$ cards, uniformly over deterministic initial decks. The conditional estimate is averaged over the actual outside-path law, rather than asserted for each individual environment. The formalization also includes the associated overlay, reset minorization, and two-color conditional constructions. The formalization covers nine routing and representation estimates for Thorp sweeps: adaptive operator and fourth-trace bounds, Casimir moments, dense truncation, sparse contact, harmonic-cycle contraction, smoothing, and three tail or sparse-saving estimates. They bound routing-density deviations and Fourier operators in dense and sparse regimes, including exponential savings in the level scale and representation dimension. The conditional high-height estimate requires a sufficiently large cutoff height $J$ that exceeds twice the number $s$ of coordinates in the fixed low block, so $J>2s$. These are the earlier nine statements associated with the paper; its changed later statements and six other result blocks are outside this scope. The formalization proves uniform representation bounds for one coordinate sweep of the Thorp shuffle. For each irreducible representation of dimension $D$, it chooses a weight between $D^{3/4}$ and $D$ and a Schatten exponent bounded by one absolute constant so that the weighted Schatten moment is at most one. The sweep's operator norm is consequently at most $D^{-c}$ for one absolute $c>0$. The supporting row–column estimate bounds the total squared overlap over all multiplicity copies on an occupied board, with explicit dependence on the row and column representation dimensions, the global dimension, the number of missing cells, and the number of rows or columns containing the global Young diagram. The paper's full physical-mixing conclusion is outside these selected representation estimates. The formalization proves a uniform trace-smoothing estimate for coordinate sweeps of the Thorp shuffle on $2^d$ cards. One absolute sweep parameter works for every $d\ge1$: the regular trace is at most $1+(2^d)^{-10}$, and the full permutation law after the corresponding fixed number of sweeps is within $\tfrac12(2^d)^{-5}$ of uniform in total variation, for every initial deck. Thus the selected upper bound uses $O(d)$ physical shuffles. The formalized result is the weighted compatibility theorem for balanced $A\times D$ rectangles, with $n=AD$ and $\sqrt n/2\le A,D\le2\sqrt n$. For arbitrary nonnegative weights on the row and column permutation groups, the normalized compatibility average is bounded by $\exp(C_0n^{54/100})$ times the product of the marginal $L^{1/\theta}$ factors, where $\theta=1-L/\log\sqrt n>0$ and the constants are absolute. Compatibility means injectivity in every original column. The bounded regular-moment and other moment/rank conclusions are not included. The formalization gives signed representation estimates for coordinate sweeps of the Thorp shuffle. For every signed occurrence of a Young diagram of size $2^d$, it bounds the logarithm of a fixed-order weighted sweep moment by a small multiple of the signed partition entropy plus an explicit remainder-size budget. The moment order is uniform over the diagrams and decompositions after the two small coefficients are fixed. The linked supporting angle bound controls the overlap of row, column, and global signed-type projections on an occupied rectangle, with explicit entropy, dimension, and missing-cell factors. These selected estimates support the paper's full-density argument; the full $L^2$ and total-variation mixing conclusion is outside them. The formalized binary-sweep theorem gives a universal power contraction in every irreducible representation: for sufficiently large $d$, the averaged sweep on $2^d$ slots has operator norm at most $D^{-g}$ in representation dimension $D$, for some $g>0$. The sign expectation is zero, and a fixed number of independent sweeps approaches uniform in total variation from every initial deck. A separate conditional moment estimate covers allowed power-of-two grids and disjoint coordinate-respecting trajectories, with its stated feasibility premise. Physical-shuffle law identification is not included. The formalization proves the paper's strict four-row permanent inequality. There are constants $4/3<p<2$ and $\varepsilon>0$ such that every probability law on $S_4$ within total-variation distance $\varepsilon$ of uniform, and with exactly uniform coordinate marginals, satisfies the permanent bound by the product of the four $L^p$ row norms for every nonnegative matrix. The exponent and neighborhood are uniform over those laws. The Thorp mixing consequence is outside this selected statement. -/
