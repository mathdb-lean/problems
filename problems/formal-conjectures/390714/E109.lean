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

- problem_id: E109
- collection: erdos
- question_id: erdos:109
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/109.lean#erdos_109
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Any $A\subseteq \mathbb{N}$ of positive upper density contains a sumset $B+C$ where both $B$ and $C$ are infinite. The Erdős sumset conjecture. Proved by Moreira, Richter, and Robertson [MRR19].
- notes: Erdos Problem 109 -- https://www.erdosproblems.com/109
- track: solved
- answer_shape: proof
- source_stem: 109
- mathdb_ref: erdos:109
- source_namespace: Erdos109
- source_theorem: erdos_109
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Pointwise

namespace Problem

abbrev Target : Prop :=
    ∀ (A : Set ℕ) (h : A.upperDensity > 0),
      ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ B + C ⊆ A

end Problem
