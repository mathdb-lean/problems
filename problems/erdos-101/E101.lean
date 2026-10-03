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

- problem_id: E101
- collection: erdos
- question_id: erdos:101
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/101.lean#erdos_101
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Given $n$ points in $\mathbb{R}^2$, no five of which are on a line, the number of lines containing four points is $o(n^2)$.
- notes: Erdos Problem 101 -- https://www.erdosproblems.com/101
- track: open
- answer_shape: proof
- source_stem: 101
- mathdb_ref: erdos:101
- source_namespace: Erdos101
- source_theorem: erdos_101
- source_category: research open
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open EuclideanGeometry Filter Asymptotics

/--
The set of lines in $\mathbb{R}^2$ containing exactly $k$ points from a given set $S$.
-/
noncomputable def linesWithPointsFor (k : ℕ) (S : Set ℝ²) : Set (AffineSubspace ℝ ℝ²) :=
  let determined_lines := { affineSpan ℝ {p, q} | (p ∈ S) (q ∈ S) (_ : p ≠ q) }
  { L ∈ determined_lines | (↑L ∩ S).ncard = k }

/--
The maximum number of lines containing exactly $4$ points among all sets $S$ of $n$
points in $\mathbb{R}^2$ satisfying the condition that no five points are collinear.
-/
noncomputable def numLinesWithFourPointMax (n : ℕ) : ℕ :=
  sSup {((linesWithPointsFor 4 S).ncard)| (S : Set ℝ²)
    (_ : S.ncard = n) (_ : S.Finite) (_ : NonCollinearFor 5 S)}

abbrev Target : Prop :=
    (fun n => (numLinesWithFourPointMax n : ℝ)) =o[atTop] (fun n => (n : ℝ)^2)

end Problem
