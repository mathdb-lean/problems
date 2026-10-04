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

- problem_id: E1049_prove
- collection: erdos
- question_id: erdos:1049
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1049.lean#erdos_1049
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $t>1$ be a rational number. Is $\sum_{n=1}^\infty\frac{1}{t^n-1}=\sum_{n=1}^\infty \frac{\tau(n)}{t^n}$ irrational, where $\tau(n)$ counts the divisors of $n$? A conjecture of Chowla.
- notes: Erdos Problem 1049 -- https://www.erdosproblems.com/1049
- track: open
- answer_shape: prove
- pair_id: E1049
- pair_role: prove
- source_stem: 1049
- mathdb_ref: erdos:1049
- source_namespace: Erdos1049
- source_theorem: erdos_1049
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open ArithmeticFunction Filter

abbrev Target : Prop :=
    ∀ t : ℚ, t > 1 → Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1))

end Problem
