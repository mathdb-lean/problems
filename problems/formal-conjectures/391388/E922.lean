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

- problem_id: E922
- collection: erdos
- question_id: erdos:922
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/922.lean#erdos_922
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k\geq 0$. Let $G$ be a graph such that every subgraph $H$ contains an independent set of size $\geq (n-k)/2$, where $n$ is the number of vertices of $H$. Must $G$ have chromatic number at most $k+2$? A question of Erdős and Hajnal [ErHa67b]. The case $k=0$ is trivial, but they could not prove this even for $k=1$. This is true, and was proved by Folkman [Fo70b]. See also [73](https://www.erdosproblems.com/73).
- notes: Erdos Problem 922 -- https://www.erdosproblems.com/922
- track: solved
- answer_shape: decide
- source_stem: 922
- mathdb_ref: erdos:922
- source_namespace: Erdos922
- source_theorem: erdos_922
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open SimpleGraph

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (k : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V),
        (∀ S : Finset V, ∃ I : Finset V, I ⊆ S ∧ (G.induce (I : Set V)).edgeSet = ∅ ∧
          (I.card : ℝ) ≥ (S.card - k : ℝ) / 2) →
        G.chromaticNumber ≤ k + 2

end Problem
