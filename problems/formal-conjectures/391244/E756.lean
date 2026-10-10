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

- problem_id: E756
- collection: erdos
- question_id: erdos:756
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/756.lean#erdos_756
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subset \mathbb{R}^2$ be a set of $n$ points. Can there be $\gg n$ many distinct distances each of which occurs for more than $n$ many pairs from $A$? The answer is yes: Bhowmick [Bh24] constructs a set of $n$ points in $\mathbb{R}^2$ such that $\lfloor\frac{n}{4}\rfloor$ distances occur at least $n+1$ times.
- notes: Erdos Problem 756 -- https://www.erdosproblems.com/756
- track: solved
- answer_shape: decide
- source_stem: 756
- mathdb_ref: erdos:756
- source_namespace: Erdos756
- source_theorem: erdos_756
- source_category: research solved
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter
open scoped EuclideanGeometry Asymptotics

namespace Problem

/-- The distances determined by `A` which occur for at least `k` many pairs of points of `A`. -/
noncomputable def richDistances (A : Finset ℝ²) (k : ℕ) : Finset ℝ :=
  (distanceSet A).filter fun d => k ≤ distanceMultiplicity A d

/-- The largest number of distinct distances that a set of `n` points in $\mathbb{R}^2$ can
determine, each of which occurs for more than `n` many pairs of points of the set. -/
noncomputable def maxRichDistances (n : ℕ) : ℕ :=
  sSup {(richDistances A (n + 1)).card | (A : Finset ℝ²) (_ : A.card = n)}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (maxRichDistances n : ℝ))

end Problem
