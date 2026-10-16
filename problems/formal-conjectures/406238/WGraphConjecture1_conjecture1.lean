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

- problem_id: WGraphConjecture1_conjecture1
- collection: wotw
- question_id: wotw:GraphConjecture1
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture1.lean#conjecture1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 1](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/) For a simple connected graph `G` the maximum number of leaves of a spanning tree satisfies `Ls(G) ≥ n(G) + 1 - 2·m(G)` where `n(G)` counts vertices and `m(G)` is the size of a maximum matching. A formal proof reduces to a spanning tree `T`. If `I` is the set of non-leaves of `T`, Hall's theorem applied to a bipartition of `T` gives a matching `M` with `|I| + 1 ≤ 2 * |M|`. Since `|V|` is the sum of the numbers of leaves and non-leaves, and every matching and leaf count constructed in `T` is admissible for the corresponding supremum in `G`, the stated inequality follows.
- notes: Written on the Wall II, problem GraphConjecture1 -- http://cms.dt.uh.edu/faculty/delavinae/research/wowII/
- track: solved
- answer_shape: proof
- source_stem: GraphConjecture1
- source_namespace: WrittenOnTheWallII.GraphConjecture1
- source_theorem: conjecture1
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

abbrev Target : Prop :=
    ∀ {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
        (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected),
      (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)

end Problem
