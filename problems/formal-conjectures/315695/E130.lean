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

- problem_id: E130
- collection: erdos
- question_id: erdos:130
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/130.lean#erdos_130
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subset\mathbb{R}^2$ be an infinite set which contains no three points on a line and no four points on a circle. Consider the graph with vertices the points in $A$, where two vertices are joined by an edge if and only if they are an integer distance apart. How large can the chromatic number and clique number of this graph be? In particular, can the chromatic number be infinite? The chromatic number can be infinite: there is an infinite general-position set whose integer-distance graph admits no finite proper colouring. How large the *clique* number can be is not addressed here.
- notes: Erdos Problem 130 -- https://www.erdosproblems.com/130
- track: solved
- answer_shape: decide
- source_stem: 130
- mathdb_ref: erdos:130
- source_namespace: Erdos130
- source_theorem: erdos_130
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open EuclideanGeometry SimpleGraph

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      ∃ A : Set ℝ², A.Infinite ∧ InGeneralPosition A ∧
        (IntegerDistancePlaneGraph A).chromaticNumber = ⊤

end Problem
