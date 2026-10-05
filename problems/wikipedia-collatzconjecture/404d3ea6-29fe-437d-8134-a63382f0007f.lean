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

- problem_id: NCollatzConjecture_collatz_conjecture
- collection: wikipedia
- question_id: wikipedia:CollatzConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/CollatzConjecture.lean#collatz_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Now form a sequence beginning with any positive integer, where each subsequent term is obtained by applying the operation defined above to the previous term. The **Collatz conjecture** states that for any positive integer $n$, there exists a natural number $m$ such that the $m$-th term of the sequence is 1.
- notes: Wikipedia: CollatzConjecture -- https://en.wikipedia.org/wiki/Collatz_conjecture
- track: open
- answer_shape: proof
- source_stem: CollatzConjecture
- source_namespace: CollatzConjecture
- source_theorem: collatz_conjecture
- source_category: research open
- source_ams: 11 37
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
Consider the following operation on the natural numbers:
If the number is even, divide it by two.
If the number is odd, triple it and add one.
-/
def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : n > 0),
      ∃ m, collatzStep^[m] n = 1

end Problem
