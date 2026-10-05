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

- problem_id: E279_prove
- collection: erdos
- question_id: erdos:279
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/279.lean#erdos_279
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k\geq 3$. Is there a choice of congruence classes $a_p\pmod{p}$ for every prime $p$ such that all sufficiently large integers can be written as $a_p+tp$ for some prime $p$ and integer $t\geq k$?
- notes: Erdos Problem 279 -- https://www.erdosproblems.com/279
- track: open
- answer_shape: prove
- pair_id: E279
- pair_role: prove
- source_stem: 279
- mathdb_ref: erdos:279
- source_namespace: Erdos279
- source_theorem: erdos_279
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∀ k : Nat, k ≥ 3 →
        ∃ a : Nat → Nat, ∃ N : Nat, (∀ p : Nat, p.Prime → a p < p) ∧
        ∀ n ≥ N, ∃ p : Nat, ∃ t ≥ k, p.Prime ∧ n = a p + t * p

end Problem
