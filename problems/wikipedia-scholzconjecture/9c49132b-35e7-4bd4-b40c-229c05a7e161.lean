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

- problem_id: NScholzConjecture_scholz_conjecture_prove
- collection: wikipedia
- question_id: wikipedia:ScholzConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/ScholzConjecture.lean#scholz_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The Scholz conjecture, also known as the Scholz-Brauer conjecture, asserts that for every positive integer $n$, the addition-chain length of $2^n - 1$ is at most $n - 1 + \ell(n)$.
- notes: Wikipedia: ScholzConjecture -- https://en.wikipedia.org/wiki/Scholz_conjecture
- track: open
- answer_shape: prove
- pair_id: NScholzConjecture_scholz_conjecture
- pair_role: prove
- source_stem: ScholzConjecture
- source_namespace: ScholzConjecture
- source_theorem: scholz_conjecture
- source_category: research open
- source_ams: 11 68
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

local notation "ℓ(" n ")" => additionChainLength n

abbrev Target : Prop :=
    ∀ (n : ℕ), 0 < n → ℓ(2 ^ n - 1) ≤ n - 1 + ℓ(n)

end Problem
