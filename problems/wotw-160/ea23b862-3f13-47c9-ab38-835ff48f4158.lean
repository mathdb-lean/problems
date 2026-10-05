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

- problem_id: W160_conjecture160
- collection: wotw
- question_id: wotw:160
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/160.lean#conjecture160
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 160](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/) For a simple connected graph $G$, $L_s(G) \ge \max_v l(v) + \max_v T(v) \cdot \chi_{C_4}(G)$ where: - $L_s(G) = \mathrm{SimpleGraph.Ls}\, G$ is the maximum number of leaves over all spanning trees of $G$, - $\max_v l(v)$ is the maximum local independence number over vertices, - $\max_v T(v)$ is the maximum number of triangles incident to any vertex, - $\chi_{C_4}(G)$ is `1` if $G$ has no cycle of length four and `0` otherwise. A formal proof uses the $C_4$-free neighborhood identity $d(v) = \lambda(v) + T(v)$ with a star/geodesic case analysis, routed through the connected-seed spanning-tree bound developed for Conjecture 2. An independent second proof, via a closest maximizer pair joined by a shortest path, is linked from the pull request that recorded the solution.
- notes: Written on the Wall II, problem 160
- track: solved
- answer_shape: proof
- source_stem: 160
- source_namespace: WrittenOnTheWallII.GraphConjecture160
- source_theorem: conjecture160
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The maximum number of triangles incident to any vertex in $G$. -/
noncomputable def maxTrianglesAtVertex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.image (numTrianglesAtVertex G)).max' (Finset.image_nonempty.mpr Finset.univ_nonempty)

open scoped Classical in
abbrev Target : Prop :=
    ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected),
      let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
      let maxT := maxTrianglesAtVertex G
      let cC4 : ℕ := if ∃ v : α, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4 then 0 else 1
      (maxL : ℝ) + (maxT : ℝ) * (cC4 : ℝ) ≤ Ls G

end Problem
