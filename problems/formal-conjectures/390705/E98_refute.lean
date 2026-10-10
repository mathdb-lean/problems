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

- problem_id: E98_refute
- collection: erdos
- question_id: erdos:98
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/98.lean#erdos_98
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $h(n)$ be such that any $n$ points in $\mathbb{R}^2$, with no three on a line and no four on a circle, determine at least $h(n)$ distinct distances. Does $h(n)/n\to \infty$?
- notes: Erdos Problem 98 -- https://www.erdosproblems.com/98
- track: open
- answer_shape: refute
- pair_id: E98
- pair_role: refute
- source_stem: 98
- mathdb_ref: erdos:98
- source_namespace: Erdos98
- source_theorem: erdos_98
- source_category: research open
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Finset EuclideanGeometry Filter

namespace Problem

/-- $h(n)$ is the minimum number of distinct distances determined by any
$n$-point set in $\mathbb{R}^2$ in general position (no three collinear, no four
cocyclic). -/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ points : Finset ℝ², points.card = n ∧
    InGeneralPosition points ∧ k = distinctDistances points}

abbrev Target : Prop :=
    ¬ (
      Tendsto (fun n : ℕ ↦ ((h n : ℝ) / (n : ℝ))) atTop atTop
    )

end Problem
