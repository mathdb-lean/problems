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

- problem_id: WGraphConjecture146_conjecture146
- collection: wotw
- question_id: wotw:GraphConjecture146
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture146.lean#conjecture146
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 146](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/) For a simple connected graph $G$, $\mathrm{tree}(G) \ge 2 \cdot \mathrm{ecc}(B) / \mathrm{rad}(G^2)$ where $\mathrm{tree}(G)$ is the number of vertices in a largest induced subtree, $\mathrm{ecc}(B)$ is the eccentricity of the boundary vertices of $G$ (`eccSet` and `maxEccentricityVertices`), and $\mathrm{rad}(G^2)$ is the radius of the square graph of $G$. We state the inequality in the form $\mathrm{tree}(G) \cdot \mathrm{rad}(G^2) \ge 2 \cdot \mathrm{ecc}(B)$ to avoid division. ## Informal proof Write $t$ for the largest induced-tree order, $r$ and $d$ for the radius and diameter of $G$, and $p$ for the eccentricity of its peripheral set. First, the distance in the graph square is $\operatorname{dist}_{G^2}(u,v)=\lceil\operatorname{dist}_G(u,v)/2\rceil$, so $\operatorname{rad}(G^2)=\lceil r/2\rceil$. A diametral geodesic is an induced path, giving $t\ge d+1$, while $p\le d-1$. These bounds settle every case except $r=2$, $d=4$, and $p=3$. In that remaining configuration, choose a centre and shortest paths to two diametral vertices and to a vertex at distance three from the peripheral set. A finite case analysis on the two possible cross-arm edges (and then the possible chords) always produces an induced tree on at least six vertices. Hence $t\,\operatorname{rad}(G^2) \ge 2p$ in the exceptional case as well.
- notes: Written on the Wall II, problem GraphConjecture146 -- http://cms.dt.uh.edu/faculty/delavinae/research/wowII/
- track: solved
- answer_shape: proof
- source_stem: GraphConjecture146
- source_namespace: WrittenOnTheWallII.GraphConjecture146
- source_theorem: conjecture146
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The radius of $G^2$ (the graph square): the minimum eccentricity over all vertices
of `graphSquare G`. -/
noncomputable def graphSquareRadius (G : SimpleGraph α) : ℕ :=
  (graphSquare G).radius.toNat

abbrev Target : Prop :=
    ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
        (hrad : 0 < graphSquareRadius G),
      2 * eccSet G (maxEccentricityVertices G : Set α) ≤
      largestInducedTreeSize G * graphSquareRadius G

end Problem
