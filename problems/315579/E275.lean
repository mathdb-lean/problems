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

- problem_id: E275
- collection: erdos
- question_id: erdos:275
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/275.lean#erdos_275
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If a finite system of $r$ congruences $\{ a_i\pmod{n_i} : 1\leq i\leq r\}$ (the $n_i$ are not necessarily distinct) covers $2^r$ consecutive integers then it covers all integers. This is best possible as the system $2^{i-1}\pmod{2^i}$ shows. This was proved independently by Selfridge and Crittenden and Vanden Eynden [CrVE70]. This was formalized in Lean by Alexeev using Aristotle.
- notes: Erdos Problem 275 -- https://www.erdosproblems.com/275
- track: solved
- answer_shape: proof
- source_stem: 275
- mathdb_ref: erdos:275
- source_namespace: Erdos275
- source_theorem: erdos_275
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Set

namespace Problem

abbrev Target : Prop :=
    ∀ (r : ℕ) (a : Fin r → ℤ) (n : Fin r → ℕ)
        (H : ∃ k : ℤ, ∀ x ∈ Ico k (k + 2 ^ r), ∃ i, x ≡ a i [ZMOD n i]) (x : ℤ),
      ∃ i, x ≡ a i [ZMOD n i]

end Problem
