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

- problem_id: WGraphConjecture176_conjecture176
- collection: wotw
- question_id: wotw:GraphConjecture176
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture176.lean#conjecture176
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII Conjecture 176 asked whether every nontrivial finite connected simple graph `G` satisfies `Ls(G) + b(G) ≥ n(G) + dist_min(G, M(G²))`. The answer is no, witnessed by `D₇`.
- notes: Written on the Wall II, problem GraphConjecture176
- track: solved
- answer_shape: decide
- source_stem: GraphConjecture176
- source_namespace: WrittenOnTheWallII.GraphConjecture176
- source_theorem: conjecture176
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open SimpleGraph

/-- The maximum-degree vertices of `G²`, presented using finite graph distance. -/
def squareMaximumDegreeVertices {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Set V :=
  let squareDegree (v : V) :=
    (Finset.univ.filter fun w => v ≠ w ∧ computable_dist G v w ≤ 2).card
  {v | squareDegree v = Finset.univ.sup squareDegree}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
          (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
            Ls G + b G ≥ (Fintype.card V : ℝ) +
              distMin G (squareMaximumDegreeVertices G)

end Problem
