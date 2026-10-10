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

- problem_id: E95
- collection: erdos
- question_id: erdos:95
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/95.lean#erdos_95
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $x_1,\ldots,x_n\in\mathbb{R}^2$ determine the set of distances $\{u_1,\ldots,u_t\}$. Suppose $u_i$ appears as the distance between $f(u_i)$ many pairs of points. Then for all $\epsilon>0$ $$\sum_i f(u_i)^2 \ll_\epsilon n^{3+\epsilon}.$$ The case when the points determine a convex polygon was solved by Altman [Al63]. Note it is trivial that $\sum f(u_i)=\binom{n}{2}$. Solved by Guth and Katz [GuKa15] who proved the upper bound $$\sum_i f(u_i)^2 \ll n^3\log n.$$ See also [94](https://www.erdosproblems.com/94).
- notes: Erdos Problem 95 -- https://www.erdosproblems.com/95
- track: solved
- answer_shape: decide
- source_stem: 95
- mathdb_ref: erdos:95
- source_namespace: Erdos95
- source_theorem: erdos_95
- source_category: research solved
- source_ams: 5 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter EuclideanGeometry

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ P : Finset ℝ²,
        ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤
          C * (P.card : ℝ) ^ (3 + ε)

end Problem
