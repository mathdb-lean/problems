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

- problem_id: E125
- collection: erdos
- question_id: erdos:125
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/125.lean#erdos_125
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Case 3: Does $A + B$ have positive upper and lower density that are equal? This is the literal interpretation of "positive density" which was falsified.
- notes: Erdos Problem 125 -- https://www.erdosproblems.com/125
- track: solved
- answer_shape: decide
- source_stem: 125
- mathdb_ref: erdos:125
- source_namespace: Erdos125
- source_theorem: erdos_125
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Nat Pointwise

namespace Problem

set_option quotPrecheck false

/--
Let $A$ be the set of integers which have only the digits $0, 1$ when written base 3,
-/
local notation "A" => { x : ℕ | (digits 3 x).toFinset ⊆ {0, 1} }
/--
and $B$ be the set of integers which have only the digits $0, 1$ when written base 4.
-/
local notation "B" => { x : ℕ | (digits 4 x).toFinset ⊆ {0, 1} }

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ (A + B).HasPosDensity

end Problem
