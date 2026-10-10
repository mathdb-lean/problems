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

- problem_id: E390_refute
- collection: erdos
- question_id: erdos:390
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/390.lean#erdos_390
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does there exists a constant `c` such that `f n - 2 * n ~ c * (n / log n)`?
- notes: Erdos Problem 390 -- https://www.erdosproblems.com/390
- track: open
- answer_shape: refute
- pair_id: E390
- pair_role: refute
- source_stem: 390
- mathdb_ref: erdos:390
- source_namespace: Erdos390
- source_theorem: erdos_390
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Nat
open Filter Asymptotics Real

namespace Problem

/-- Let `f n` be the smallest integer for which `n!` can be represented as the product of distinct
integers greater than n, the largest of which is `f n`. -/
noncomputable def f (n : ℕ) : ℕ := sInf {m : ℕ | ∃ k, ∃ f : ℕ → ℕ, StrictMono f ∧
  n < f 0 ∧ f (k - 1) = m ∧ ∏ i < k, f i = n !}

abbrev Target : Prop :=
    ¬ (
      ∃ c,
        (fun n => f n - 2 * n : ℕ → ℝ) ~[atTop] (fun n => c * n / log (n : ℝ))
    )

end Problem
