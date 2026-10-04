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

- problem_id: E800
- collection: erdos
- question_id: erdos:800
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/800.lean#erdos_800
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $G$ is a graph on $n$ vertices which has no two adjacent vertices of degree $\geq 3$ then $$R(G)\ll n,$$ where the implied constant is absolute. A problem of Burr and Erdős. Solved in the affirmative by Alon [Al94].
- notes: Erdos Problem 800 -- https://www.erdosproblems.com/800
- track: solved
- answer_shape: decide
- source_stem: 800
- mathdb_ref: erdos:800
- source_namespace: Erdos800
- source_theorem: erdos_800
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ C > (0 : ℝ), ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
          Fintype.card V = n →
          (∀ u v, G.Adj u v → ¬(3 ≤ G.degree u ∧ 3 ≤ G.degree v)) →
          (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ C * n

end Problem
