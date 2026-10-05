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

- problem_id: WGraphConjecture145_conjecture145
- collection: wotw
- question_id: wotw:GraphConjecture145
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture145.lean#conjecture145
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 145](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/) For a simple connected graph $G$, $\mathrm{tree}(G) \ge 2 \cdot \mathrm{ecc}(B) / \lambda_{\min}(\overline{G})$ where $\mathrm{tree}(G)$ is the number of vertices in a largest induced subtree, $\mathrm{ecc}(B)$ is the eccentricity of the boundary vertices (`eccSet` and `boundaryVertices`), and $\lambda_{\min}(\overline{G})$ is the minimum local independence number of the complement graph. We state the inequality in the form $\mathrm{tree}(G) \cdot \mathrm{lMin}(\overline{G}) \ge 2 \cdot \mathrm{ecc}(B)$ to avoid division. ## Provenance Solved by Dominic Dabish. ProofOrchestrator, using OpenAI GPT-5.6 Thinking, assisted with the mathematical argument and Lean formalization; all formal claims were checked by the pinned Lean compiler.
- notes: Written on the Wall II, problem GraphConjecture145
- track: solved
- answer_shape: proof
- source_stem: GraphConjecture145
- source_namespace: WrittenOnTheWallII.GraphConjecture145
- source_theorem: conjecture145
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- `localIndependenceMin G` is the minimum over all vertices of the local independence
number `indepNeighborsCard G v`. This equals $\mathrm{lMin}$ from DeLaVina's notation. -/
noncomputable def localIndependenceMin (G : SimpleGraph α) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (indepNeighborsCard G)

abbrev Target : Prop :=
    ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
        (hlMin : 0 < localIndependenceMin Gᶜ),
      2 * eccSet G (maxEccentricityVertices G : Set α) ≤
      largestInducedTreeSize G * localIndependenceMin Gᶜ

end Problem
