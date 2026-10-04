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

- problem_id: E392
- collection: erdos
- question_id: erdos:392
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/392.lean#erdos_392
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A(n)$ denote the least value of $t$ such that $$ n! = a_1 \cdots a_t $$ with $a_1 \leq \cdots \leq a_t\leq n^2$. Then $$ A(n) = \frac{n}{2} - \frac{n}{2\log n} + o\left(\frac{n}{\log n}\right). $$
- notes: Erdos Problem 392 -- https://www.erdosproblems.com/392
- track: solved
- answer_shape: proof
- source_stem: 392
- mathdb_ref: erdos:392
- source_namespace: Erdos392
- source_theorem: erdos_392
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

open scoped Nat

namespace Problem

abbrev Target : Prop :=
    ∀ (A : ℕ → ℕ) (h : ∀ n > 0,
        IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
          Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)),
      ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n)

end Problem
