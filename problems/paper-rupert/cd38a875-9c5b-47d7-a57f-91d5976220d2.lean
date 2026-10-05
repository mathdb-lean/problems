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

- problem_id: RRupert_is_every_convex_polyhedron_rupert
- collection: paper
- question_id: paper:Rupert
- source: formal-conjectures
- source_locator: FormalConjectures/Paper/Rupert.lean#is_every_convex_polyhedron_rupert
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: There exists a convex polyhedron with nonempty interior for which the Rupert property does not hold.
- notes: Problem from Rupert -- https://www.researchgate.net/publication/314715434_Platonic_Passages
- track: solved
- answer_shape: decide
- source_stem: Rupert
- source_namespace: Rupert
- source_theorem: is_every_convex_polyhedron_rupert
- source_category: research solved
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open scoped Matrix

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

scoped notation "ℝ²" => Fin 2 → ℝ
scoped notation "ℝ³" => Fin 3 → ℝ

/--
The result of transforming a subset of ℝ³ by a chosen rotation and offset,
and then projected to ℝ².
-/
def transformed_shadow (X : Set ℝ³) (offset : ℝ²) (rotation : SO3) : Set ℝ² :=
  (fun p ↦ offset + (rotation *ᵥ p) ∘ Fin.castSucc) '' X

/--
A convex polyhedron (given as a finite collection of vertices) is Rupert if
there are two rotations in ℝ³ (called "inner" and "outer") and a translation in ℝ²
such that the "inner shadow" (the projection to ℝ² of the inner rotation applied
to the polyhedron, then translated) fits in the interior of the "outer shadow"
(the projection to ℝ² of the outer rotation applied to the polyhedron)

[Note: The restriction to (polyhedra determined by the convex hulls of)
*finite* sets of vertices here is deliberate. Were we to generalize to
arbitrary subsets of ℝⁿ we'd probably want to make the containment
relation more strict, e.g.
  closure inner_shadow ⊆ interior outer_shadow
to rule out, e.g. the open ball being Rupert. However, we didn't
observe any such generalization in the literature yet, so we stuck to
what was in the citations above.]
-/
def IsRupert (vertices : Finset ℝ³) : Prop :=
   ∃ (inner_rotation : SO3) (inner_offset : ℝ²) (outer_rotation : SO3),
   let inner_shadow := transformed_shadow (convexHull ℝ vertices) inner_offset inner_rotation
   let outer_shadow := transformed_shadow (convexHull ℝ vertices) 0 outer_rotation
   inner_shadow ⊆ interior outer_shadow

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (vertices : Finset ℝ³),
       (interior (convexHull ℝ vertices : Set ℝ³)).Nonempty → IsRupert vertices

end Problem
