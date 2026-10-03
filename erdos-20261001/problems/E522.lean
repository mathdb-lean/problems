/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 The mathdb-lean Authors.

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

import MathdbUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: E522
- collection: erdos
- question_id: erdos:522
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/522.lean#erdos_522
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(z)=\sum_{0\leq k\leq n} \epsilon_k z^k$ be a random polynomial, where $\epsilon_k\in \{-1,1\}$ independently uniformly at random for $0\leq k\leq n$. Is it true that, if $R_n$ is the number of roots of $f(z)$ in $\{ z\in \mathbb{C} : \lvert z\rvert \leq 1\}$, then $$ \frac{R_n}{n/2}\to 1 $$ almost surely? There is some ambiguity as to whether the intended coefficient set is $\{-1, 1\}$ or $\{0, 1\}$, see `erdos_522.variants.zero_one` for the alternate version. This is true. Proofs were posted on the erdosproblems.com forum in April 2026 [Ch26], [KZ26], and Lean proofs were given independently in September 2026 [Ka26], [Ki26]. More generally, [Ka26] proves an almost-sure radial law: the number of roots in $\{\lvert z\rvert \le 1 + x/n\}$ is $\Phi(x)\,n + o(n)$ for every $x$, where $\Phi(x) = \tfrac12\left(1 + \coth x - \tfrac1x\right)$. This problem is the case $x = 0$.
- notes: Erdos Problem 522 -- https://www.erdosproblems.com/522
- track: solved
- answer_shape: decide
- source_stem: 522
- mathdb_ref: erdos:522
- source_namespace: Erdos522
- source_theorem: erdos_522
- source_category: research solved
- source_ams: 12 60
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open MeasureTheory Filter
open scoped ProbabilityTheory Topology Real

namespace Problem

/--
A sequence of *Kac coefficients* over a subset `S` of a field `k` is a countably infinite sequence
of independent random variables, each uniformly distributed over `S` with respect to the reference
measure `μ`. The default reference measure is the counting measure, so that for a finite set `S`
each coefficient takes every value of `S` with probability `1 / |S|`.

Such a sequence determines a *Kac polynomial* of degree `n` for each `n`, which is the random
polynomial given by `KacCoefficients.polynomial`.
-/
@[ext]
structure KacCoefficients
    {k : Type*} [Field k] [MeasurableSpace k] (S : Set k)
    (Ω : Type*) [MeasureSpace Ω] (μ : Measure k := Measure.count) where
  toFun : ℕ → Ω → k
  h_indep : ProbabilityTheory.iIndepFun toFun ℙ
  h_unif : ∀ i, MeasureTheory.pdf.IsUniform (toFun i) S ℙ μ

variable {k : Type*} [Field k] [MeasurableSpace k] (S : Set k)
    (Ω : Type*) [MeasureSpace Ω] (μ : Measure k := Measure.count)

/--
We can always view a Kac polynomial as a random variable on `ℕ`.
-/
instance : FunLike (KacCoefficients S Ω μ) ℕ (Ω → k) where
  coe P := P.toFun
  coe_injective P Q h := by aesop

namespace KacCoefficients

open scoped Polynomial

variable {S Ω} {μ : Measure k}

/--
The random polynomial associated to a sequence `c : KacCoefficients S Ω μ` of Kac coefficients
given by `∑ i ∈ Finset.range (n + 1), c i z^i`.
-/
noncomputable def polynomial (c : KacCoefficients S Ω μ) (n : ℕ) :
    Ω → k[X] := fun ω => ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (c i ω)

/--
The random multiset of roots associated to a Kac polynomial
-/
noncomputable def roots (c : KacCoefficients S Ω μ) (n : ℕ) : Ω → Multiset k :=
    fun ω => (c.polynomial n ω).roots

/-- Counts the number of roots of a Kac polynomial in the unit disk with multiplicity. -/
noncomputable def numRootsInUnitDisk [PseudoMetricSpace k] (c : KacCoefficients S Ω μ) (n : ℕ)
    (ω : Ω) : ℕ :=
  open scoped Classical in
  (c.roots n ω).countP (· ∈ Metric.closedBall 0 1)

end KacCoefficients

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (c : KacCoefficients ({-1, 1} : Set ℂ) Ω),
      ℙ {ω | atTop.Tendsto (fun n : ℕ ↦ (2 * c.numRootsInUnitDisk n ω : ℝ) / n) (𝓝 1)} = 1

end Problem
