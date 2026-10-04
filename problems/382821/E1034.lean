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

- problem_id: E1034
- collection: erdos
- question_id: erdos:1034
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1034.lean#erdos_1034
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be a graph on $n$ vertices with $>n^2/4$ many edges. Must there be a triangle $T$ in $G$ and vertices $y_1,\ldots,y_t$, where $t>(\frac{1}{2}-o(1))n$, such that every $y_i$ is joined to at least two vertices of $T$? A conjecture of Erdős and Faudree; a stronger version of [905]. This has been solved in the negative by Ma and Tang [MaTa25], who construct a graph with $n$ vertices and $>n^2/4$ edges in which every triangle has at most $(2-(5/2)^{1/2}+o(1))n$ vertices adjacent to at least two of its vertices (note that $2-(5/2)^{1/2}\approx 0.4189$).
- notes: Erdos Problem 1034 -- https://www.erdosproblems.com/1034
- track: solved
- answer_shape: decide
- source_stem: 1034
- mathdb_ref: erdos:1034
- source_namespace: Erdos1034
- source_theorem: erdos_1034
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter

namespace Problem

/--
`JoinedToTwo G T Y` holds when every vertex of `Y` is joined to at least two (distinct)
vertices of `T`.
-/
def JoinedToTwo {V : Type*} (G : SimpleGraph V) (T Y : Finset V) : Prop :=
  ∀ y ∈ Y, ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ G.Adj y u ∧ G.Adj y v

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
          (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
            ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
              JoinedToTwo G T Y ∧ (1 / 2 - ε) * (n : ℝ) < (Y.card : ℝ)

end Problem
