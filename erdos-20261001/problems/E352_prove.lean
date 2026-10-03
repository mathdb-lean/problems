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

- problem_id: E352_prove
- collection: erdos
- question_id: erdos:352
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/352.lean#erdos_352
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there some $c > 0$ such that every measurable $A \subseteq \mathbb{R}^2$ of measure $\geq c$ contains the vertices of a triangle of area 1?
- notes: Erdos Problem 352 -- https://www.erdosproblems.com/352
- track: open
- answer_shape: prove
- pair_id: E352
- pair_role: prove
- source_stem: 352
- mathdb_ref: erdos:352
- source_namespace: Erdos352
- source_theorem: erdos_352
- source_category: research open
- source_ams: 51
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped EuclideanGeometry
open scoped ProbabilityTheory

namespace Problem

abbrev Target : Prop :=
    ∃ c > (0: ℝ), ∀ A : Set ℝ², MeasurableSet A → ℙ A ≥ c.toEReal
       → (∃ t : Affine.Triangle ℝ ℝ²,
           (∀ p : Fin 3, t.points p ∈ A) ∧
           EuclideanGeometry.triangle_area (t.points 0) (t.points 1) (t.points 2) = 1)

end Problem
