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

- problem_id: NPrimeTriplets_prime_triplets_refute
- collection: wikipedia
- question_id: wikipedia:PrimeTriplets
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/PrimeTriplets.lean#prime_triplets
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there infinitely many tuples of three consecutive primes $(p, q, r)$ such that $r - p = 6$?
- notes: Wikipedia: PrimeTriplets -- https://en.wikipedia.org/wiki/Prime_triplet#Conjecture_on_prime_triplets
- track: open
- answer_shape: refute
- pair_id: NPrimeTriplets_prime_triplets
- pair_role: refute
- source_stem: PrimeTriplets
- source_namespace: PrimeTriplets
- source_theorem: prime_triplets
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ¬ (
      {p : ℕ | Prime p ∧ (Prime (p + 2) ∨ Prime (p + 4)) ∧ Prime (p + 6)}.Infinite
    )

end Problem
