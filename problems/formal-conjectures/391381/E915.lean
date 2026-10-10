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

- problem_id: E915
- collection: erdos
- question_id: erdos:915
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/915.lean#erdos_915
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be a graph with $1+n(m-1)$ vertices and $1+n\binom{m}{2}$ edges. Must $G$ contain two points which are connected by $m$ disjoint paths? A conjecture of Bollobás and Erdős [BoEr62]. This would be the best possible, as demonstrated by $n$ copies of $K_m$ which share a single vertex (but are otherwise disjoint). It is unclear whether disjoint here is to mean edge-disjoint or (internally) vertex-disjoint. The above construction is valid for either interpretation. This is the internally vertex-disjoint reading. It is trivial for $m = 2$, and was proved for $m = 3$ by Bártfai [Ba60] and for $m = 4$ by Bollobás [Bo66]. Leonard [Le73] disproved this conjecture for $m=5$, giving an explicit counterexample with $57$ vertices and $141$ edges, and Mader [Ma73] disproved the conjecture in general for all $m \geq 6$. Sørensen and Thomassen [SoTh74] proved that the conjectured bound of Bollobás and Erdős holds if the graph is $3$-connected.
- notes: Erdos Problem 915 -- https://www.erdosproblems.com/915
- track: solved
- answer_shape: decide
- source_stem: 915
- mathdb_ref: erdos:915
- source_namespace: Erdos915
- source_theorem: erdos_915
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open SimpleGraph

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ m n : ℕ, 2 ≤ m → 1 ≤ n → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
          Fintype.card V = 1 + n * (m - 1) → G.edgeSet.ncard = 1 + n * m.choose 2 →
            ∃ u v : V, u ≠ v ∧ ∃ P : Finset (G.Walk u v), P.card = m ∧ (∀ p ∈ P, p.IsPath) ∧
              (P : Set (G.Walk u v)).Pairwise InternallyDisjoint

end Problem
