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

- problem_id: E1098
- collection: erdos
- question_id: erdos:1098
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1098.lean#erdos_1098
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be a group and $\Gamma=\Gamma(G)$ be the non-commuting graph, with vertices the elements of $G$ and an edge between $g$ and $h$ if and only if $g$ and $h$ do not commute, $gh\neq hg$. If $\Gamma$ contains no infinite complete subgraph, then is there a finite bound on the size of complete subgraphs of $\Gamma$? This was solved by Neumann [Ne76], who proved that $\Gamma$ contains no infinite complete subgraph if and only if the centre of the group has finite index, and noted that if the centre has index $n$ then $\Gamma$ contains no complete subgraph on $>n$ vertices.
- notes: Erdos Problem 1098 -- https://www.erdosproblems.com/1098
- track: solved
- answer_shape: decide
- source_stem: 1098
- mathdb_ref: erdos:1098
- source_namespace: Erdos1098
- source_theorem: erdos_1098
- source_category: research solved
- source_ams: 5 20
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/-- The non-commuting graph $\Gamma = \Gamma(G)$ of a group `G`, with vertices the elements of `G`
and an edge between `g` and `h` if and only if `g` and `h` do not commute, $gh \neq hg$. -/
def nonCommutingGraph (G : Type*) [Group G] : SimpleGraph G where
  Adj g h := g * h ≠ h * g
  symm.symm := fun _ _ h => h.symm

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (G : Type*) [Group G],
          (∀ s : Set G, (nonCommutingGraph G).IsClique s → s.Finite) →
            ∃ n : ℕ, ∀ s : Finset G, (nonCommutingGraph G).IsClique (s : Set G) → s.card ≤ n

end Problem
