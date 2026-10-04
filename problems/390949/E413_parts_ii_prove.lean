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

- problem_id: E413_parts_ii_prove
- collection: erdos
- question_id: erdos:413
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/413.lean#erdos_413.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does there exist some `ε > 0` such that there are infinitely many `ε`-barriers for `ω`?
- notes: Erdos Problem 413 -- https://www.erdosproblems.com/413
- track: open
- answer_shape: prove
- pair_id: E413_parts_ii
- pair_role: prove
- source_stem: 413
- mathdb_ref: erdos:413
- source_namespace: Erdos413
- source_theorem: erdos_413.parts.ii
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open ArithmeticFunction
open scoped omega Omega

namespace Problem

/-- `IsBarrier f n` means `n` is a barrier for the real-valued function `f`,
i.e. `(m : ℝ) + f m ≤ (n : ℝ)` for all `m < n`. -/
def IsBarrier (f : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ m < n, (m : ℝ) + f m ≤ n

/-- `expProd n` is `∏ kᵢ` when `n = ∏ pᵢ ^ kᵢ`, i.e. the product of the prime exponents of `n`. -/
def expProd (n : ℕ) : ℕ :=
  n.factorization.prod fun _ e => e

abbrev Target : Prop :=
    (∃ ε > (0 : ℝ), { n | IsBarrier (fun n => ε * ω n) n }.Infinite)

end Problem
