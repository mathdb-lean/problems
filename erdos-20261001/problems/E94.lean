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

- problem_id: E94
- collection: erdos
- question_id: erdos:94
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/94.lean#erdos_94
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Suppose $n$ points in $\mathbb{R}^2$ determine a convex polygon and the set of distances between them is $\{u_1,\ldots,u_t\}$. Suppose $u_i$ appears as the distance between $f(u_i)$ many pairs of points. Then $$\sum_i f(u_i)^2 \ll n^3.$$ In [Er97c] Erdős claims that Fishburn solved this, but gives no reference.
- notes: Erdos Problem 94 -- https://www.erdosproblems.com/94
- track: solved
- answer_shape: proof
- source_stem: 94
- mathdb_ref: erdos:94
- source_namespace: Erdos94
- source_theorem: erdos_94
- source_category: research solved
- source_ams: 5 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter EuclideanGeometry

namespace Problem

/-- The regular $n$-gon inscribed in the unit circle. -/
noncomputable def regularNGon (n : ℕ) : Finset ℝ² :=
  (Finset.range n).image fun k : ℕ =>
    !₂[Real.cos (2 * Real.pi * k / n), Real.sin (2 * Real.pi * k / n)]

abbrev Target : Prop :=
    ∃ C > (0 : ℝ), ∀ P : Finset ℝ², ConvexIndep (P : Set ℝ²) →
        ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤ C * (P.card : ℝ) ^ 3

end Problem
