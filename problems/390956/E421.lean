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

- problem_id: E421
- collection: erdos
- question_id: erdos:421
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/421.lean#erdos_421
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: There exists a sequence $1 \le d_1 < d_2 < \dots$ with density 1 such that all products $\prod_{u \le i \le v} d_i$ are distinct. This was solved affirmatively; see [Pratt26].
- notes: Erdos Problem 421 -- https://www.erdosproblems.com/421
- track: solved
- answer_shape: decide
- source_stem: 421
- mathdb_ref: erdos:421
- source_namespace: Erdos421
- source_theorem: erdos_421
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Set

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ (d : ℕ → ℕ), StrictMono d ∧ 1 ≤ d 0 ∧ HasDensity (Set.range d) 1 ∧
        {(u, v) : ℕ × ℕ | u ≤ v}.InjOn fun (u, v) => ∏ i ∈ Finset.Icc u v, d i

end Problem
