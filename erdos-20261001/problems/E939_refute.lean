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

- problem_id: E939_refute
- collection: erdos
- question_id: erdos:939
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/939.lean#erdos_939
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $r≥4$ then can the sum of $r-2$ coprime $r$-powerful numbers ever be itself $r$-powerful?
- notes: Erdos Problem 939 -- https://www.erdosproblems.com/939
- track: open
- answer_shape: refute
- pair_id: E939
- pair_role: refute
- source_stem: 939
- mathdb_ref: erdos:939
- source_namespace: Erdos939
- source_theorem: erdos_939
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat

namespace Problem

/--
A set `S` belongs to `Erdos939Sums r` if it meets the following criteria:
- The elements are positive. `0` has no prime factors, so it is vacuously `r`-powerful, and
  the source means positive integers.
- The size of the set is `$|S| = r - 2$`.
- The elements of the set are coprime (their greatest common divisor is 1).
- Every element in `S` is an `$r$-powerful` number.
- The sum of the elements in `S`, i.e., `$\sum_{s \in S} s$`, is also an `$r$-powerful` number.

The summands are taken to be distinct (`S` is a `Finset`). The source does not say whether
repeated summands are allowed; all known examples and constructions use distinct summands.
-/
def Erdos939Sums (r : ℕ) :=
    {S : Finset ℕ | S.card = r - 2 ∧ S.Coprime ∧ r.Full (∑ s ∈ S, s) ∧
      ∀ s ∈ S, 0 < s ∧ r.Full s}

abbrev Target : Prop :=
    ¬ (
      ∀ r ≥ 4, (Erdos939Sums r).Nonempty
    )

end Problem
