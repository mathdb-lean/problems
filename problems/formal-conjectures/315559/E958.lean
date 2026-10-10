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

import MathDBUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: E958
- collection: erdos
- question_id: erdos:958
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/958.lean#erdos_958
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subset \mathbb{R}^2$ be a finite set of size $n$, and let $\{d_1,\ldots,d_k\}$ be the set of distances determined by $A$. Let $f(d)$ be the multiplicity of $d$, that is, the number of unordered pairs from $A$ of distance $d$ apart. Is it true that $k=n-1$ and $\{f(d_i)\}=\{n-1,\ldots,1\}$ if and only if $A$ is a set of equidistant points on a line or a circle? Erdős conjectured that the answer is no, and other such configurations exist. This was proved by Clemen, Dumitrescu, and Liu [CDL25], who observed that equidistant points on a short circular arc on a circle of radius $1$, together with the centre, are also an example. The classification is asked for all sufficiently large $n$. Small exceptions such as $\{(0,0), (1,0), (0,1), (0,-1)\}$ exist, so the negative answer asserts counterexamples of arbitrarily large size, as in [CDL25].
- notes: Erdos Problem 958 -- https://www.erdosproblems.com/958
- track: solved
- answer_shape: decide
- source_stem: 958
- mathdb_ref: erdos:958
- source_namespace: Erdos958
- source_theorem: erdos_958
- source_category: research solved
- source_ams: 5 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Finset EuclideanGeometry

namespace Problem

/-- `A` is a set of equidistant points on a line: there are a point `a` and a non-zero direction
`v` such that `A` consists of the points `a + i • v` for `0 ≤ i < #A`. -/
def IsEquidistantOnLine (A : Finset ℝ²) : Prop :=
  ∃ a v : ℝ², v ≠ 0 ∧ (A : Set ℝ²) = {x | ∃ i : ℕ, i < #A ∧ x = a + (i : ℝ) • v}

/-- `A` is a set of equidistant points on a circle: there are a centre `c`, a radius `r > 0`, an
initial angle `θ` and a non-zero angular step `α` such that `A` consists of the points of the
circle of centre `c` and radius `r` at the angles `θ + i * α` for `0 ≤ i < #A`. -/
def IsEquidistantOnCircle (A : Finset ℝ²) : Prop :=
  ∃ (c : ℝ²) (r θ α : ℝ), 0 < r ∧ α ≠ 0 ∧ (A : Set ℝ²) =
    {x | ∃ i : ℕ, i < #A ∧
      x = c + r • (!₂[Real.cos (θ + (i : ℝ) * α), Real.sin (θ + (i : ℝ) * α)])}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℝ², #A = n →
          ((#(distanceSet A) = n - 1 ∧
                (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (n - 1)) →
            (IsEquidistantOnLine A ∨ IsEquidistantOnCircle A))

end Problem
