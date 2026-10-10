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

- problem_id: E550
- collection: erdos
- question_id: erdos:550
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/550.lean#erdos_550
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $m_1\leq\cdots\leq m_k$ and $n$ be sufficiently large. If $T$ is a tree on $n$ vertices and $G$ is the complete multipartite graph with vertex class sizes $m_1,\ldots,m_k$ then prove that $$R(T,G)\leq (\chi(G)-1)(R(T,K_{m_1,m_2})-1)+m_1.$$ This problem is #16 in Ramsey Theory in the graphs problem collection. Li [Li26] proved this, combining an off-Turán tree-embedding theorem with a compactness theorem for bounded-rank hypergraph obstructions. The linked formal proof states the bound for trees on an arbitrary finite vertex type and with `K_{m_1,m_2}` written as a complete multipartite graph with two parts; the statement below is the special case `V = Fin n`.
- notes: Erdos Problem 550 -- https://www.erdosproblems.com/550
- track: solved
- answer_shape: proof
- source_stem: 550
- mathdb_ref: erdos:550
- source_namespace: Erdos550
- source_theorem: erdos_550
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

abbrev Target : Prop :=
    ∀ (k : ℕ) (hk : 2 ≤ k) (m : Fin k → ℕ) (hm : Monotone m)
      (hm_pos : ∀ i, 0 < m i),
      ∀ᶠ n : ℕ in atTop,
        ∀ (T : SimpleGraph (Fin n)), T.IsTree →
          SimpleGraph.graphRamsey T
            (SimpleGraph.completeMultipartiteGraph (fun i ↦ Fin (m i))) ≤
            (k - 1) * (SimpleGraph.graphRamsey T
              (completeBipartiteGraph (Fin (m ⟨0, by omega⟩)) (Fin (m ⟨1, by omega⟩))) - 1) +
                m ⟨0, by omega⟩

end Problem
