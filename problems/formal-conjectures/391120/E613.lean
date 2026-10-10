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

- problem_id: E613
- collection: erdos
- question_id: erdos:613
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/613.lean#erdos_613
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Erdős Problem 613:** Let $n \geq 3$ and $G$ be a graph with $\binom{2n+1}{2} - \binom{n}{2} - 1$ edges. Must $G$ be the union of a bipartite graph and a graph with maximum degree less than $n$?
- notes: Erdos Problem 613 -- https://www.erdosproblems.com/613
- track: solved
- answer_shape: decide
- source_stem: 613
- mathdb_ref: erdos:613
- source_namespace: Erdos613
- source_theorem: erdos_613
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      ∀ n ≥ 3, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V), [DecidableRel G.Adj] →
        G.edgeFinset.card = Nat.choose (2 * n + 1) 2 - Nat.choose n 2 - 1 →
        ∃ (B D : SimpleGraph V), [DecidableRel B.Adj] → [DecidableRel D.Adj] →
          G = B ⊔ D ∧ B.IsBipartite ∧ ∀ v, D.degree v < n

end Problem
