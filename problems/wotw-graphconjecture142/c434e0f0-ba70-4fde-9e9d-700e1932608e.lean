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

- problem_id: WGraphConjecture142_conjecture142
- collection: wotw
- question_id: wotw:GraphConjecture142
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture142.lean#conjecture142
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 142](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/): For a simple connected graph $G$, $\mathrm{tree}(G) \ge (2/3) \cdot \mathrm{girth}(G) + \mathrm{ecc}(B)$ where $\mathrm{tree}(G)$ is the largest induced tree size, $\mathrm{girth}(G)$ is the length of the shortest cycle ($0$ if acyclic), $B$ is the set of boundary vertices (those of maximum eccentricity), and $\mathrm{ecc}(B)$ is the eccentricity of the set $B$. **Proof sketch.** The proof first strengthens the real-valued target to the integral bound $$ \mathrm{ecc}(B) + \mathrm{girth}(G) - \lfloor \mathrm{girth}(G) / 3 \rfloor \leq \mathrm{tree}(G). $$ For a cyclic graph, start with a shortest cycle $K$. It is chordless, so removing one vertex leaves an induced path on $\mathrm{girth}(G)-1$ vertices. Shortest paths from selected vertices to $K$ are called *descents*. Pairwise noninteracting descents attach to the retained cycle path as disjoint branches. If two descents interact, the proof cuts at the first interaction encountered from the outer endpoint toward the cycle and splices the paths there. Minimality of that interaction makes the retained prefix disjoint and nonadjacent to the first descent; geodesicity excludes chords, while girth at least five rules out extra cross-edges and cycle attachments. Choose a vertex realizing $\mathrm{ecc}(B)$ and two endpoints of a diametral geodesic. Either two of their descents interact, directly giving a sufficiently long spliced tree, or all three are separate, in which case a three-point distance inequality forces their total length to be large enough. This proves the integral bound in the main range. Girths three and four, small $\mathrm{ecc}(B)$, and the two remaining congruence cases are handled by separate geodesic/cycle certificates with one or two descents; the acyclic case follows from a diametral path. Finally, $$ \mathrm{girth}(G)-\lfloor\mathrm{girth}(G)/3\rfloor = \lceil 2\,\mathrm{girth}(G)/3\rceil \geq 2\,\mathrm{girth}(G)/3, $$ which gives the stated real-valued inequality. The argument was developed with assistance from ChatGPT Pro. The linked Lean 4 formalization was produced with assistance from OpenAI Codex and checked by Lean.
- notes: Written on the Wall II, problem GraphConjecture142
- track: solved
- answer_shape: proof
- source_stem: GraphConjecture142
- source_namespace: WrittenOnTheWallII.GraphConjecture142
- source_theorem: conjecture142
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
    ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected),
      let B : Set α := (maxEccentricityVertices G : Set α)
      (2 : ℝ) / 3 * (G.girth : ℝ) + (eccSet G B : ℝ) ≤ (largestInducedTreeSize G : ℝ)

end Problem
