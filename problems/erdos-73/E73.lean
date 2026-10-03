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

- problem_id: E73
- collection: erdos
- question_id: erdos:73
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/73.lean#erdos_73
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k\ge 0$. Let $G$ be a graph such that every subgraph $H$ contains an independent set of size $\ge (n-k)/2$, where $n$ is the number of vertices of $H$. Must $G$ be the union of a bipartite graph and $O_k(1)$ many vertices? Proved by Reed [Re99]. The linked formal proof (Alexeev and Codex, following Reed's mangoes-and-blueberries argument) states the hypothesis as `∀ H : G.Subgraph, H.verts.ncard ≤ 2 * H.coe.indepNum + k` and the conclusion as `(G.induce Dᶜ).IsBipartite`, for graphs on `Fin n` (and, equivalently, on any finite vertex type); this implies the statement below.
- notes: Erdos Problem 73 -- https://www.erdosproblems.com/73
- track: solved
- answer_shape: decide
- source_stem: 73
- mathdb_ref: erdos:73
- source_namespace: Erdos73
- source_theorem: erdos_73
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
        ∀ (k : ℕ), ∃ (C : ℕ),
          ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
            (∀ (S : Finset V), ∃ (I : Finset V), I ⊆ S ∧ (G.induce (I : Set V)).edgeSet = ∅ ∧
              (I.card : ℝ) ≥ (S.card - k : ℝ) / 2) →
            ∃ (D : Finset V), D.card ≤ C ∧
              (G.induce (D : Set V)ᶜ).Colorable 2

end Problem
