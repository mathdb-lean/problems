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

- problem_id: WGraphConjecture309_conjecture309
- collection: wotw
- question_id: wotw:GraphConjecture309
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture309.lean#conjecture309
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does every finite simple connected graph $G$ of order greater than two satisfy $$ \gamma_t(G) \leq \frac{1}{2}\left( \max_v(\operatorname{distEven}(v)-\operatorname{evenHorizontal}(v))+ \min_{e\in E(\overline G)}|N_{\overline G}(e)|\right)? $$ Gebendorfer disproved the statement with the family $C_5[K_k]$, $k \geq 3$.
- notes: Written on the Wall II, problem GraphConjecture309 -- http://cms.dt.uh.edu/faculty/delavinae/research/wowII/
- track: solved
- answer_shape: decide
- source_stem: GraphConjecture309
- source_namespace: WrittenOnTheWallII.GraphConjecture309
- source_theorem: conjecture309
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The number of edges whose endpoints are at the same even distance from $v$. -/
def evenHorizontal (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (G.edgeFinset.filter fun e =>
    let distances := e.toFinset.image (G.computable_dist v)
    distances.card = 1 ∧ ∃ d ∈ distances, Even d).card

/-- The maximum of $\operatorname{distEven}(v)-\operatorname{evenHorizontal}(v)$. -/
noncomputable def maxEvenCorrection (G : SimpleGraph V) [Nonempty V]
    [DecidableRel G.Adj] : ℤ :=
  (Finset.univ.image
    (fun v => (G.distEven v : ℤ) - (evenHorizontal G v : ℤ))).max' (by simp)

/-- The minimum complement-edge neighborhood-union order, when a complement edge exists. -/
def minComplementEdgeNeighborhood (G : SimpleGraph V)
    [DecidableRel G.Adj] : Option ℕ :=
  Gᶜ.edgeFinset.image
    (fun e => Sym2.lift ⟨fun u w =>
      (Gᶜ.neighborFinset u ∪ Gᶜ.neighborFinset w).card,
      fun u w => by
        change (Gᶜ.neighborFinset u ∪ Gᶜ.neighborFinset w).card =
          (Gᶜ.neighborFinset w ∪ Gᶜ.neighborFinset u).card
        rw [Finset.union_comm]⟩ e) |>.min

/--
The universal inequality proposed in WOWII Conjecture 309. The `Option`-valued
minimum makes the statement vacuous for complete graphs, whose complements
have no edge; this totalization does not affect the counterexample.
-/
def conjecture309Statement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 2 < Fintype.card V →
    ∀ mt ∈ minComplementEdgeNeighborhood G,
      (G.totalDominationNumber : ℝ) ≤
        ((maxEvenCorrection G : ℝ) + (mt : ℝ)) / 2

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ conjecture309Statement

end Problem
