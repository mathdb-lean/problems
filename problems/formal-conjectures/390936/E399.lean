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

- problem_id: E399
- collection: erdos
- question_id: erdos:399
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/399.lean#erdos_399
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that there are no solutions to `n! = x^k ± y^k` with `x,y,n ∈ ℕ`, `x*y > 1`, and `k > 2`? The answer is no: Jonas Barfield found the counterexample `10! = 48^4 - 36^4` (equivalently, `10! + 36^4 = 48^4`). This is discussed in problem D2 of Guy's collection [Gu04]. This was formalized in Lean by Lu using Codex.
- notes: Erdos Problem 399 -- https://www.erdosproblems.com/399
- track: solved
- answer_shape: decide
- source_stem: 399
- mathdb_ref: erdos:399
- source_namespace: Erdos399
- source_theorem: erdos_399
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Nat

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ¬ ∃ (n x y k : ℕ), 1 < x * y ∧ 2 < k ∧ (n ! = x ^ k + y ^ k ∨ n ! + y ^ k = x ^ k)

end Problem
