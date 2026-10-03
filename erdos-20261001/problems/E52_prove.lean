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

- problem_id: E52_prove
- collection: erdos
- question_id: erdos:52
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/52.lean#erdos_52
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A$ be a finite set of integers. Is it true that for every $\epsilon>0$ $\max( \lvert A+A\rvert,\lvert AA\rvert)\gg_\epsilon \lvert A\rvert^{2-\epsilon}?$
- notes: Erdos Problem 52 -- https://www.erdosproblems.com/52
- track: open
- answer_shape: prove
- pair_id: E52
- pair_role: prove
- source_stem: 52
- mathdb_ref: erdos:52
- source_namespace: Erdos52
- source_theorem: erdos_52
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Pointwise

namespace Problem

abbrev Target : Prop :=
    ∀ (ε : ℝ), 0 < ε → ε < 1 → ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ),
        (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)

end Problem
