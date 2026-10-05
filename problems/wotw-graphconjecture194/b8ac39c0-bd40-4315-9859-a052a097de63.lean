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

- problem_id: WGraphConjecture194_conjecture194
- collection: wotw
- question_id: wotw:GraphConjecture194
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture194.lean#conjecture194
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 194](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/) For a simple connected graph `G`, if `α(G) ≤ 1 + l_avg(G)`, then `G` has a Hamiltonian path. Here `α(G) = G.indepNum` is the independence number, and `l_avg(G) = averageIndepNeighbors G` is the average over all vertices of the independence number of the neighbourhood. A Hamiltonian path is a walk visiting every vertex exactly once. The answer is no, as witnessed by the 18-vertex graph described above. Counterexample (Graph6): `Q~~~~~~~~~~~~}~}^~??G??_??_`
- notes: Written on the Wall II, problem GraphConjecture194
- track: solved
- answer_shape: decide
- source_stem: GraphConjecture194
- source_namespace: WrittenOnTheWallII.GraphConjecture194
- source_theorem: conjecture194
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open SimpleGraph

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
          (G : SimpleGraph α) (_h : G.Connected),
          (G.indepNum : ℝ) ≤ 1 + averageIndepNeighbors G →
          ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

end Problem
