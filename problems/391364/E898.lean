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

- problem_id: E898
- collection: erdos
- question_id: erdos:898
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/898.lean#erdos_898
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $A,B,C\in \mathbb{R}^2$ form a triangle and $P$ is a point in the interior then, if $N$ is where the perpendicular from $P$ to $AB$ meets the triangle, and similarly for $M$ and $L$, $$ \overline{PA}+\overline{PB}+\overline{PC}\geq 2(\overline{PM}+\overline{PN}+\overline{PL}). $$ Conjectured by Erdős in 1932 (according to [Er82e]) and proved by Mordell soon afterwards, now known as the Erdős-Mordell inequality.
- notes: Erdos Problem 898 -- https://www.erdosproblems.com/898
- track: solved
- answer_shape: proof
- source_stem: 898
- mathdb_ref: erdos:898
- source_namespace: Erdos898
- source_theorem: erdos_898
- source_category: research solved
- source_ams: 51
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Affine EuclideanGeometry

namespace Problem

abbrev Target : Prop :=
    ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C])
        (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²)))
        (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction)
        (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction)
        (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction),
      dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)

end Problem
