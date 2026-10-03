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

- problem_id: E881_refute
- collection: erdos
- question_id: erdos:881
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/881.lean#erdos_881
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let `A ⊂ ℕ` be an additive basis of order `k` which is minimal in the sense that if `B ⊂ A` is any infinite set, then `A \ B` is not a basis of order `k`. Must there exist an infinite `B ⊂ A` such that `A \ B` is an additive basis of order `k + 1`?
- notes: Erdos Problem 881 -- https://www.erdosproblems.com/881
- track: open
- answer_shape: refute
- pair_id: E881
- pair_role: refute
- source_stem: 881
- mathdb_ref: erdos:881
- source_namespace: Erdos881
- source_theorem: erdos_881
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Set

namespace Problem

/--
We interpret "additive basis of order `k`" as an asymptotic additive basis of order `k`,
using the predicate `Set.IsAsymptoticAddBasisOfOrder` from additive combinatorics.

A *minimal* additive basis of order `k` is a set `A` such that
* `A` is an asymptotic additive basis of order `k`, and
* for every infinite subset `B ⊆ A`, the complement `A \ B` is *not*
  an asymptotic additive basis of order `k`.
-/
def IsMinimalAsymptoticAddBasisOfOrder (k : ℕ) (A : Set ℕ) : Prop :=
  A.IsAsymptoticAddBasisOfOrder k ∧
    ∀ ⦃B : Set ℕ⦄, B ⊆ A → B.Infinite → ¬ (A \ B).IsAsymptoticAddBasisOfOrder k

abbrev Target : Prop :=
    ¬ (
      ∀ (k : ℕ) (A : Set ℕ),
        IsMinimalAsymptoticAddBasisOfOrder k A →
          ∃ (B : Set ℕ), B ⊆ A ∧ B.Infinite ∧
            (A \ B).IsAsymptoticAddBasisOfOrder (k + 1)
    )

end Problem
