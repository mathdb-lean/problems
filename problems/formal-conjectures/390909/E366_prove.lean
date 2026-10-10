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

- problem_id: E366_prove
- collection: erdos
- question_id: erdos:366
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/366.lean#erdos_366
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there any $2$-full $n$ such that $n+1$ is $3$-full?
- notes: Erdos Problem 366 -- https://www.erdosproblems.com/366
- track: open
- answer_shape: prove
- pair_id: E366
- pair_role: prove
- source_stem: 366
- mathdb_ref: erdos:366
- source_namespace: Erdos366
- source_theorem: erdos_366
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: exists_three_full_then_two_full
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
Note that $8$ is $3$-full and $9$ is 2-full.
-/
@[category test, AMS 11]
theorem exists_three_full_then_two_full : ∃ n > 0, (3).Full n ∧ (2).Full (n + 1) := by
  use 8
  norm_num +contextual [Nat.Full, Nat.primeFactors, Nat.primeFactorsList]

abbrev Target : Prop :=
    ∃ n > 0, (2).Full n ∧ (3).Full (n + 1)

end Problem
