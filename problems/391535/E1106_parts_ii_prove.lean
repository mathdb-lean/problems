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

- problem_id: E1106_parts_ii_prove
- collection: erdos
- question_id: erdos:1106
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1106.lean#erdos_1106.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $p(n)$ be the partition number of $n$ and $F(n)$ be the number of distinct prime factors of $∏_{i= 1} ^ {n} p(n)$, $F(n)>n$ for sufficiently large $n$.
- notes: Erdos Problem 1106 -- https://www.erdosproblems.com/1106
- track: open
- answer_shape: prove
- pair_id: E1106_parts_ii
- pair_role: prove
- source_stem: 1106
- mathdb_ref: erdos:1106
- source_namespace: Erdos1106
- source_theorem: erdos_1106.parts.ii
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat Finset Filter Topology

namespace Problem

/-- The partition function p(n) is the number of ways to write n as a sum of positive
integers (where the order of the summands does not matter). -/
def p : ℕ → ℕ := fun n => Fintype.card (Nat.Partition n)

abbrev Target : Prop :=
    ∀ᶠ n in atTop, #(∏ i ∈ Icc 1 n, p i).primeFactors > n

end Problem
