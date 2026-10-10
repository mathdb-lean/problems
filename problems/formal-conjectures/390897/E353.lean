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

- problem_id: E353
- collection: erdos
- question_id: erdos:353
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/353.lean#erdos_353
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq \mathbb{R}^2$ be a measurable set with infinite measure. Must $A$ contain the vertices of an isosceles trapezoid of area $1$? What about an isosceles triangle, or a right-angled triangle, or a cyclic quadrilateral, or a convex polygon with congruent sides? Koizumi [Ko25] has resolved this question, proving that any set with infinite measure must contain the vertices of an isosceles trapezoid, an isosceles triangle, and a right-angled triangle, all of area $1$. This statement formalizes the leading question, for isosceles trapezoids; the remaining configurations are given as variants below. The area of a polygon is taken to be the Lebesgue measure of the convex hull of its vertices.
- notes: Erdos Problem 353 -- https://www.erdosproblems.com/353
- track: solved
- answer_shape: decide
- source_stem: 353
- mathdb_ref: erdos:353
- source_namespace: Erdos353
- source_theorem: erdos_353
- source_category: research solved
- source_ams: 28 51
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Affine EuclideanGeometry MeasureTheory

open scoped Real

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ A : Set ℝ², MeasurableSet A → volume A = ⊤ →
          ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ d ∈ A,
            IsIsoscelesTrapezoid a b c d ∧
            volume (convexHull ℝ {a, b, c, d}) = 1

end Problem
