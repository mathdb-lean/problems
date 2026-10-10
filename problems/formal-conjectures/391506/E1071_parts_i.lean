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

- problem_id: E1071_parts_i
- collection: erdos
- question_id: erdos:1071
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1071.lean#erdos_1071.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Can a finite set of disjoint unit segments in a unit square be maximal? Solved affirmatively by [Da85], who gave an explicit construction. This was formalized in Lean by Alexeev using Aristotle and ChatGPT.
- notes: Erdos Problem 1071 -- https://www.erdosproblems.com/1071
- track: solved
- answer_shape: decide
- source_stem: 1071
- mathdb_ref: erdos:1071
- source_namespace: Erdos1071
- source_theorem: erdos_1071.parts.i
- source_category: research solved
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Set Metric EuclideanGeometry Order

namespace Problem

/-- Two segments are disjoint if they only intersect at their endpoints (if at all). -/
def SegmentsDisjoint (seg1 seg2 : ℝ² × ℝ²) : Prop :=
  segment ℝ seg1.1 seg1.2 ∩ segment ℝ seg2.1 seg2.2 ⊆ {seg1.1, seg1.2, seg2.1, seg2.2}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ S : Finset (ℝ² × ℝ²),
      Maximal (fun T : Finset (ℝ² × ℝ²) =>
        (∀ seg ∈ T, dist seg.1 seg.2 = 1 ∧
          seg.1 0 ∈ Icc 0 1 ∧ seg.1 1 ∈ Icc 0 1 ∧
          seg.2 0 ∈ Icc 0 1 ∧ seg.2 1 ∈ Icc 0 1) ∧
          (T : Set (ℝ² × ℝ²)).Pairwise SegmentsDisjoint) S

end Problem
