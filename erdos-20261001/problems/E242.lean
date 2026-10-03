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

- problem_id: E242
- collection: erdos
- question_id: erdos:242
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/242.lean#erdos_242
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For every $n>2$ there exist distinct integers $1 ≤ x < y < z$ such that $\frac 4 n = \frac 1 x + \frac 1 y + \frac 1 z$.
- notes: Erdos Problem 242 -- https://www.erdosproblems.com/242
- track: open
- answer_shape: proof
- source_stem: 242
- mathdb_ref: erdos:242
- source_namespace: Erdos242
- source_theorem: erdos_242
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Topology

namespace Problem

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 2 < n),
      ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
        (4 / n : ℚ) = 1 / x + 1 / y + 1 / z

end Problem
