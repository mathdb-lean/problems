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

- problem_id: E660_prove
- collection: erdos
- question_id: erdos:660
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/660.lean#erdos_660
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $x_1, \ldots, x_n \in \mathbb{R}^3$ be the vertices of a convex polyhedron. Are there at least $$(1 - o(1)) \frac{n}{2}$$ many distinct distances between the $x_i$? The $(1 - o(1)) \frac{n}{2}$ lower bound is formalised as: for every $\varepsilon > 0$, every set of $n$ vertices of a convex polyhedron with $n$ sufficiently large determines at least $(1 - \varepsilon) \frac{n}{2}$ distinct distances.
- notes: Erdos Problem 660 -- https://www.erdosproblems.com/660
- track: open
- answer_shape: prove
- pair_id: E660
- pair_role: prove
- source_stem: 660
- mathdb_ref: erdos:660
- source_namespace: Erdos660
- source_theorem: erdos_660
- source_category: research open
- source_ams: 51 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped EuclideanGeometry

namespace Problem

/--
`P` is the set of vertices of a (full-dimensional) convex polyhedron in $\mathbb{R}^3$: the points
are in convex position and they affinely span $\mathbb{R}^3$ (so the polyhedron is genuinely
three-dimensional).
-/
def IsPolyhedronVertices (P : Finset ℝ³) : Prop :=
  ConvexIndependent ℝ ((↑) : ↥(P : Set ℝ³) → ℝ³) ∧ affineSpan ℝ (P : Set ℝ³) = ⊤

abbrev Target : Prop :=
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, ∀ P : Finset ℝ³,
        P.card = n → IsPolyhedronVertices P →
        (1 - ε) * ((n : ℝ) / 2) ≤ (distinctDistances P : ℝ)

end Problem
