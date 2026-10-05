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

- problem_id: WGraphConjecture181_conjecture181
- collection: wotw
- question_id: wotw:GraphConjecture181
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture181.lean#conjecture181
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII Conjecture 181 asked whether every nontrivial finite connected simple graph `G` satisfies `Ls G + b G ≥ G.indepNum + deg_avg(B(G²))`. The answer is no, witnessed by `T(7) = L(K₇)`.
- notes: Written on the Wall II, problem GraphConjecture181
- track: solved
- answer_shape: decide
- source_stem: GraphConjecture181
- source_namespace: WrittenOnTheWallII.GraphConjecture181
- source_theorem: conjecture181
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open SimpleGraph

/-- The average degree, in `G²`, of the maximum-eccentricity vertices of `G²`. -/
noncomputable def squarePeripheryAverage {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ := by
  classical
  let square := graphSquare G
  let periphery := Finset.univ.filter fun v => v ∈ maxEccentricityVertices square
  exact (∑ v ∈ periphery, ((square.neighborFinset v).card : ℝ)) / periphery.card

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
          (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
            Ls G + b G ≥ G.indepNum + squarePeripheryAverage G

end Problem
