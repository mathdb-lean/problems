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

- problem_id: WGraphConjecture2_conjecture2
- collection: wotw
- question_id: wotw:GraphConjecture2
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture2.lean#conjecture2
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 2](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/) For a simple connected graph $G$, $Ls(G) \ge 2 \cdot (l(G) - 1)$ where $l(G)$ is the average independence number of the neighbourhoods of the vertices of $G$. A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763), where an informal proof is also provided. Another formal proof combines a spanning-tree leaf bound from connected domination with an ordered-pair double-counting argument for adjacent neighbourhoods. A third formal proof starts from a triangle-free spanning subgraph of $G$ with the maximum number of edges. Maximality bounds the neighbourhood independence number of each vertex by its degree in that subgraph; an edge whose endpoint degrees sum to at least $2 \cdot l(G)$ then carries a double star, which is acyclic and extends to a spanning tree with at least $2 \cdot (l(G) - 1)$ leaves.
- notes: Written on the Wall II, problem GraphConjecture2 -- http://cms.dt.uh.edu/faculty/delavinae/research/wowII/
- track: solved
- answer_shape: proof
- source_stem: GraphConjecture2
- source_namespace: WrittenOnTheWallII.GraphConjecture2
- source_theorem: conjecture2
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

open scoped Classical in
abbrev Target : Prop :=
    ∀ (G : SimpleGraph α) (h : G.Connected),
      2 * (averageIndepNeighbors G - 1) ≤ Ls G

end Problem
