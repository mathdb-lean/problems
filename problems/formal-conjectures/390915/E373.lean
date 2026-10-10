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

- problem_id: E373
- collection: erdos
- question_id: erdos:373
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/373.lean#erdos_373
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Show that the equation `n!=a_1!a_2!···a_k!`, with `n−1 > a_1 ≥ a_2 ≥ ··· ≥ a_k`, has only finitely many solutions.
- notes: Erdos Problem 373 -- https://www.erdosproblems.com/373
- track: open
- answer_shape: proof
- source_stem: 373
- mathdb_ref: erdos:373
- source_namespace: Erdos373
- source_theorem: erdos_373
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Nat

namespace Problem

/--
Let `S` be the set of non-trivial solutions to the equation `n! = a₁! ··· aₖ!`
such that `a₁ ≥ ... ≥ aₖ` and `n-1 > a₁`.
-/
abbrev S : Set (ℕ × List ℕ) :=
  {(n, l) | n ! = (l.map Nat.factorial).prod ∧ l.Pairwise (· ≥ ·)
    ∧ l.headI < (n - 1 : ℕ) ∧ ∀ a ∈ l, 1 < a }

abbrev Target : Prop :=
    S.Finite

end Problem

-- Formalisation note: at the time of writing, the website states "Erdős proved that this problem
