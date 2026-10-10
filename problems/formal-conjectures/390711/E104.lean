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

- problem_id: E104
- collection: erdos
- question_id: erdos:104
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/104.lean#erdos_104
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Given $n$ points in $\mathbb{R}^2$ the number of distinct unit circles containing at least three points is $o(n^2)$.
- notes: Erdos Problem 104 -- https://www.erdosproblems.com/104
- track: open
- answer_shape: proof
- source_stem: 104
- mathdb_ref: erdos:104
- source_namespace: Erdos104
- source_theorem: erdos_104
- source_category: research open
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter
open scoped EuclideanGeometry

namespace Problem

open EuclideanGeometry

/-- The number of distinct unit circles containing at least three points of `P`. -/
noncomputable def unitCircleCount (P : Finset ℝ²) : ℕ :=
  Set.ncard {s : Sphere ℝ² | s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard}

/-- The set of unit-circle counts attained by configurations of `n` points in the plane. -/
noncomputable def possibleUnitCircleCounts (n : ℕ) : Set ℕ :=
  {k | ∃ P : Finset ℝ², P.card = n ∧ unitCircleCount P = k}

/-- The maximum number of qualifying unit circles attained by a configuration of `n` points. -/
noncomputable def maxUnitCircleCount (n : ℕ) : ℕ :=
  sSup (possibleUnitCircleCounts n)

abbrev Target : Prop :=
    (fun n : ℕ => (maxUnitCircleCount n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ 2)

end Problem
