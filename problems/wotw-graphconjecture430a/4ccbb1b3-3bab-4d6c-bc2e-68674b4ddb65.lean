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

- problem_id: WGraphConjecture430a_conjecture430a
- collection: wotw
- question_id: wotw:GraphConjecture430a
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture430a.lean#conjecture430a
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII Conjecture 430a asked whether every connected graph `G` of order greater than three satisfies `i(G) ≤ α(G[N(C)]) + 2 floor(CW(G)-1)`. The answer is no, witnessed by a nonuniform `P₇` clique blow-up.
- notes: Written on the Wall II, problem GraphConjecture430a
- track: solved
- answer_shape: decide
- source_stem: GraphConjecture430a
- source_namespace: WrittenOnTheWallII.GraphConjecture430a
- source_theorem: conjecture430a
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open SimpleGraph

/-- The center of a finite graph. -/
noncomputable def centerFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => G.eccent v = G.radius

/-- DeLaViña's `N(S)`: the union of open vertex neighborhoods. This may
intersect `S`. -/
def setNeighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  Finset.univ.filter fun v => ∃ u ∈ S, G.Adj u v

/-- The exact rational Caro--Wei sum. -/
def caroWei {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  ∑ v : V, 1 / ((G.degree v + 1 : ℕ) : ℚ)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
          G.Connected → 3 < Fintype.card V →
            (G.indepDominationNumber : ℤ) ≤
              ((G.induce
                (setNeighborhood G (centerFinset G) : Set V)).indepNum : ℤ) +
                2 * ⌊caroWei G - 1⌋

end Problem
