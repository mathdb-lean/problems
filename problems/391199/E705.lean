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

- problem_id: E705
- collection: erdos
- question_id: erdos:705
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/705.lean#erdos_705
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be a finite unit distance graph in $\mamthbb{R}^2$. Is there some $k$ such that if $G$ has girth $≥ k$, then $\chi(G) ≤ 3$? The general case was solved by O'Donnell [OD99], who constructed finite unit distance graphs with chromatic number $4$ and arbitrarily large girth.
- notes: Erdos Problem 705 -- https://www.erdosproblems.com/705
- track: solved
- answer_shape: decide
- source_stem: 705
- mathdb_ref: erdos:705
- source_namespace: Erdos705
- source_theorem: erdos_705
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open scoped EuclideanGeometry
open SimpleGraph

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ k, ∀ V : Set ℝ², V.Finite →
      (UnitDistancePlaneGraph V).girth ≥ k → (UnitDistancePlaneGraph V).chromaticNumber ≤ 3

end Problem
