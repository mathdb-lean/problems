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

- problem_id: E579_refute
- collection: erdos
- question_id: erdos:579
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/579.lean#erdos_579
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\delta > 0$. If $n$ is sufficiently large and $G$ is a graph on $n$ vertices with no $K_{2,2,2}$ (the octahedron) and at least $\delta n^2$ edges, must $G$ contain an independent set of size $\gg_\delta n$? This is a problem of Erdős, Hajnal, Sós, and Szemerédi [EHSS83]. It is **open**; they proved the statement for $\delta > 1/8$ (see `erdos_579.variants.ehss_large_delta`), and the difficulty is to push the edge-density threshold down to an arbitrary $\delta > 0$. Here $K_{2,2,2}$ is the complete tripartite graph with all parts of size $2$, encoded as `completeMultipartiteGraph (fun _ : Fin 3 => Fin 2)`; "contains no $K_{2,2,2}$" is expressed via `SimpleGraph.Free`.
- notes: Erdos Problem 579 -- https://www.erdosproblems.com/579
- track: open
- answer_shape: refute
- pair_id: E579
- pair_role: refute
- source_stem: 579
- mathdb_ref: erdos:579
- source_namespace: Erdos579
- source_theorem: erdos_579
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter SimpleGraph

namespace Problem

/-- The octahedron $K_{2,2,2}$: the complete tripartite graph with all three parts of
size $2$. -/
abbrev octahedron : SimpleGraph (Σ _ : Fin 3, Fin 2) :=
  completeMultipartiteGraph (fun _ : Fin 3 => Fin 2)

open scoped Classical in
abbrev Target : Prop :=
    ¬ (
      ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
            ∀ G : SimpleGraph (Fin n), octahedron.Free G →
              δ * (n : ℝ) ^ 2 ≤ G.edgeFinset.card →
                c * n ≤ (G.indepNum : ℝ)
    )

end Problem
