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

- problem_id: E1108_parts_ii_refute
- collection: erdos
- question_id: erdos:1108
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1108.lean#erdos_1108.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does the set $A = \left\{ \sum_{n\in S}n! : S\subset \mathbb{N}\text{ finite}\right\}$ of all finite sums of distinct factorials contain only finitely many powerful numbers?
- notes: Erdos Problem 1108 -- https://www.erdosproblems.com/1108
- track: open
- answer_shape: refute
- pair_id: E1108_parts_ii
- pair_role: refute
- source_stem: 1108
- mathdb_ref: erdos:1108
- source_namespace: Erdos1108
- source_theorem: erdos_1108.parts.ii
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat Filter BigOperators

namespace Problem

/--
The set $A = \left\{ \sum_{n\in S}n! : S\subset \mathbb{N}\text{ finite}\right\}$ of all finite
sums of distinct factorials.
-/
def FactorialSums : Set ℕ :=
  {m : ℕ | ∃ S : Finset ℕ, m = ∑ n ∈ S, n.factorial}

/--
A number is powerful if each prime factor appears with exponent at least 2.
-/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

abbrev Target : Prop :=
    ¬ (
      {a ∈ FactorialSums | IsPowerful a}.Finite
    )

end Problem
