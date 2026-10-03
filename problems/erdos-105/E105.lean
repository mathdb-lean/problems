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

- problem_id: E105
- collection: erdos
- question_id: erdos:105
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/105.lean#erdos_105
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A,B\subset \mathbb{R}^2$ be disjoint sets of size $n$ and $n-3$ respectively, with not all of $A$ contained on a single line. Is there a line which contains at least two points from $A$ and no points from $B$? This has been disproved by Xichuan in the comments, who has found three explicit counterexamples.
- notes: Erdos Problem 105 -- https://www.erdosproblems.com/105
- track: solved
- answer_shape: decide
- source_stem: 105
- mathdb_ref: erdos:105
- source_namespace: Erdos105
- source_theorem: erdos_105
- source_category: research solved
- source_ams: 5 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open EuclideanGeometry

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ A B : Finset ℝ², Disjoint A B → A.card = B.card + 3 →
          ¬ Collinear ℝ (A : Set ℝ²) →
          ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ ∀ b ∈ B, b ∉ line[ℝ, p, q]

end Problem
