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

- problem_id: E549
- collection: erdos
- question_id: erdos:549
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/549.lean#erdos_549
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $T$ is a tree which is a bipartite graph with $k$ vertices in one class and $2k$ vertices in the other class then $$R(T)=4k-1.$$ This is false: Norin, Sun, and Zhao [NSZ16] have proved that if $T$ is the union of two stars on $k$ and $2k$ vertices, with an edge joining the centre of the two stars, then $R(T)\geq (4.2-o(1))k$, and conjectured that $R(T)=(4.2+o(1))k$. This problem is #15 in Ramsey Theory in the graphs problem collection.
- notes: Erdos Problem 549 -- https://www.erdosproblems.com/549
- track: solved
- answer_shape: decide
- source_stem: 549
- mathdb_ref: erdos:549
- source_namespace: Erdos549
- source_theorem: erdos_549
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
        ∀ (k : ℕ) (hk : 2 ≤ k) (T : SimpleGraph (Fin k ⊕ Fin (2 * k))),
          T.IsTree →
          (∀ x₁ x₂, ¬ T.Adj (Sum.inl x₁) (Sum.inl x₂)) →
          (∀ y₁ y₂, ¬ T.Adj (Sum.inr y₁) (Sum.inr y₂)) →
          SimpleGraph.diagonalGraphRamsey T = 4 * k - 1

end Problem
