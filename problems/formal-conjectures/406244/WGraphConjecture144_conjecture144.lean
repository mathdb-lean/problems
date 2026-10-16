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

- problem_id: WGraphConjecture144_conjecture144
- collection: wotw
- question_id: wotw:GraphConjecture144
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture144.lean#conjecture144
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 144](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/) For a simple connected graph $G$, $\mathrm{tree}(G) \ge \mathrm{girth}(G) - 1 + \mathrm{ecc}(\mathrm{Centers})$ where $\mathrm{tree}(G)$ is the largest induced tree size, $\mathrm{girth}(G)$ is the length of the shortest cycle ($0$ if acyclic), $\mathrm{Centers} = G.\mathrm{center}$ is the set of vertices with minimum eccentricity (the center of $G$), and $\mathrm{ecc}(\mathrm{Centers})$ is the eccentricity of the center set — the maximum distance from any non-center vertex to the nearest center vertex. **Proof sketch.** Let $g = \mathrm{girth}(G)$ and $e = \mathrm{ecc}(G, \mathrm{center}(G))$. The acyclic and $e = 0$ cases are immediate. If $g \le e + 2$, the formalized Bacsó--Tuza induced-path argument, with an elementary $e = 1$ case, produces an induced tree on at least $2e + 1$ vertices. Since $g - 1 + e \le 2e + 1$, this proves the result. Suppose instead that $e + 3 \le g$, and fix a shortest cycle $C$. Removing one vertex of $C$ leaves an induced tree on $g - 1$ vertices. Analyze the connected components outside $C$. If one has at least $e$ vertices, it supplies an attached rooted induced tree of order $e$. Otherwise, let $D$ be the sum of the components' attachment depths. If $D \ge e$, select pairwise edge-separated rooted branches of total order $e$ and attach them to $C$, deleting a suitable cycle vertex. If $D < e$, shortest-cycle contact restrictions bound corresponding exclusion arcs. Their complement consists of central cycle vertices and $D$-dominates the graph, forcing $e \le D$, a contradiction. Finite graph search was used only during discovery to test candidate structural lemmas and reject false proof templates; no finite-search result is used in the universal proof.
- notes: Written on the Wall II, problem GraphConjecture144 -- http://cms.dt.uh.edu/faculty/delavinae/research/wowII/
- track: solved
- answer_shape: proof
- source_stem: GraphConjecture144
- source_namespace: WrittenOnTheWallII.GraphConjecture144
- source_theorem: conjecture144
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
      (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤ (largestInducedTreeSize G : ℝ)

end Problem
