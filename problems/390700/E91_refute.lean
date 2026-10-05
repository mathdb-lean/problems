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

- problem_id: E91_refute
- collection: erdos
- question_id: erdos:91
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/91.lean#erdos_91
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Suppose $A\subset \mathbb{R}^2$ has $\lvert A\rvert=n$ and minimises the number of distinct distances between points in $A$. Prove that for large $n$ there are at least two (and probably many) such $A$ which are non-similar.
- notes: Erdos Problem 91 -- https://www.erdosproblems.com/91
- track: open
- answer_shape: refute
- pair_id: E91
- pair_role: refute
- source_stem: 91
- mathdb_ref: erdos:91
- source_namespace: Erdos91
- source_theorem: erdos_91
- source_category: research open
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Finset EuclideanGeometry Filter

namespace Problem

/-- A set $A$ is 'optimal' if it has $n$ points and achieves the minimum distance count. -/
noncomputable def IsOptimal (A : Finset ℝ²) (n : ℕ) : Prop :=
  A.card = n ∧ distinctDistances A = minimalDistinctDistances ℝ² n

/-- Two finite sets of points in $\mathbb{R}^2$ are similar if one can be mapped to the other by a
DilationEquiv. -/
def DilationEquivSimilar (A B : Finset ℝ²) : Prop :=
  ∃ f : ℝ² ≃ᵈ ℝ², (f '' A) = B

/-- Equilateral triangle with unit side length, resting on the x-axis with one vertex at the origin. -/
noncomputable def equiTriangle : Finset ℝ² := {!₂[0, 0], !₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2]}

noncomputable def unitSquare : Finset ℝ² := {!₂[0, 0], !₂[0, 1], !₂[1, 0], !₂[1, 1]}

/-- Regular 7-gon with unit side length, touching both axes in the first quadrant. -/
noncomputable def circleSeven : Finset ℝ² :=
  let r := 1 / (2 * Real.sin (Real.pi / 7))
  let cx := r * Real.cos (Real.pi / 7)
  let cy := r * Real.sin (4 * Real.pi / 7)
  (Finset.range 7).image fun k : ℕ =>
    !₂[r * Real.cos (2 * Real.pi * ↑k / 7) + cx, r * Real.sin (2 * Real.pi * ↑k / 7) + cy]

/-- Wheel graph on 7 vertices (center + regular hexagon) with unit side length,
touching both axes in the first quadrant. -/
noncomputable def wheelSeven : Finset ℝ² :=
  {!₂[1, Real.sqrt 3 / 2],
   !₂[2, Real.sqrt 3 / 2],
   !₂[3 / 2, Real.sqrt 3],
   !₂[1 / 2, Real.sqrt 3],
   !₂[0, Real.sqrt 3 / 2],
   !₂[1 / 2, 0],
   !₂[3 / 2, 0]}

/--
The predicate on $n$ asserting all $A, B\subset \mathbb{R}^2$,
with $\lvert A\rvert=n = \lvert B\rvert$, which minimise the number of distinct points for all sets
with $n$ elements are similar.
-/
def UniqueMinimizer (n : ℕ) : Prop :=
  ∀ A B : Finset ℝ², IsOptimal A n → IsOptimal B n → DilationEquivSimilar A B

abbrev Target : Prop :=
    ¬ (
      (∀ᶠ n : ℕ in atTop, ¬ UniqueMinimizer n)
    )

end Problem
