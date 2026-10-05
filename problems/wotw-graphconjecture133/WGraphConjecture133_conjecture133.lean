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

- problem_id: WGraphConjecture133_conjecture133
- collection: wotw
- question_id: wotw:GraphConjecture133
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture133.lean#conjecture133
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 133](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/): For a simple connected graph $G$, $\operatorname{path}(G) \ge \operatorname{rad}(G) + (\mathrm{avg}_v\, l(v))^{cC_4(G)}$, where $\operatorname{path}(G)$ is the path number of the graph (number of vertices of a largest induced path), $\operatorname{rad}(G)$ is the radius (minimum eccentricity, as a natural number), $\mathrm{avg}_v\, l(v) = l(G)$ is the average independence number of vertex neighbourhoods, and $cC_4(G)$ is the $C_4$-free characteristic function (1 if $G$ is $C_4$-free, not necessarily induced, and 0 otherwise).
- notes: Written on the Wall II, problem GraphConjecture133 -- http://cms.dt.uh.edu/faculty/delavinae/research/wowII/
- track: open
- answer_shape: proof
- source_stem: GraphConjecture133
- source_namespace: WrittenOnTheWallII.GraphConjecture133
- source_theorem: conjecture133
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

abbrev Target : Prop :=
    ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected),
      let rad := G.radius.toNat
      let hasC4 := ∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a
      let cC4 : ℕ := if hasC4 then 0 else 1
      (rad : ℝ) + l G ^ cC4 ≤ (path G : ℝ)

end Problem
