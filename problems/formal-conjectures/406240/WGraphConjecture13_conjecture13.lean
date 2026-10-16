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

- problem_id: WGraphConjecture13_conjecture13
- collection: wotw
- question_id: wotw:GraphConjecture13
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture13.lean#conjecture13
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 13](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/) For a simple connected graph `G`, the size `b(G)` of a largest induced bipartite subgraph satisfies `b(G) ≥ diam(G) + max_{v ∈ V} l(v) - 1`, where `diam(G)` is the diameter of `G` and `l(v) = indepNeighborsCard G v` is the independence number of the neighbourhood of `v`.
- notes: Written on the Wall II, problem GraphConjecture13 -- http://cms.dt.uh.edu/faculty/delavinae/research/wowII/
- track: solved
- answer_shape: proof
- source_stem: GraphConjecture13
- source_namespace: WrittenOnTheWallII.GraphConjecture13
- source_theorem: conjecture13
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

abbrev Target : Prop :=
    ∀ (G : SimpleGraph α) (h : G.Connected),
      letI maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
      (G.diam : ℝ) + (maxL : ℝ) - 1 ≤ b G

end Problem
