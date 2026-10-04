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

- problem_id: E600_parts_i_refute
- collection: erdos
- question_id: erdos:600
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/600.lean#erdos_600.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $r \geq 2$. Is it true that $e(n,r+1) - e(n,r) \to \infty$ as $n \to \infty$?
- notes: Erdos Problem 600 -- https://www.erdosproblems.com/600
- track: open
- answer_shape: refute
- pair_id: E600_parts_i
- pair_role: refute
- source_stem: 600
- mathdb_ref: erdos:600
- source_namespace: Erdos600
- source_theorem: erdos_600.parts.i
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter
open scoped Topology

namespace Problem

open scoped Classical in
/--
Let $e(n,r)$ be minimal such that every graph on $n$ vertices with at least $e(n,r)$ edges,
each edge contained in at least one triangle, must have an edge contained in at least
$r$ triangles.
-/
def Erdos600Prop (n : ℕ) (e : ℕ) (r : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.edgeFinset.card ≥ e →
  (∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) →
  ∃ uv ∈ G.edgeFinset, r ≤ (G.trianglesContaining uv).card

noncomputable def eFunction (n : ℕ) (r : ℕ) : ℕ := sInf {e : ℕ | Erdos600Prop n e r}

abbrev Target : Prop :=
    ¬ (
      ∀ r : ℕ, 2 ≤ r →
        Tendsto (fun (n : ℕ) ↦ (eFunction n (r + 1) : ℝ) - (eFunction n r : ℝ)) atTop atTop
    )

end Problem
