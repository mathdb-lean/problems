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

- problem_id: E29
- collection: erdos
- question_id: erdos:29
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/29.lean#erdos_29
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there an explicit construction of a set $A\subseteq \mathbb{N}$ such that $A+A=\mathbb{N}$ but $1_A\ast 1_A(n)=o(n^\epsilon)$ for every $\epsilon>0$? The existence of such a set was asked by Sidon to Erdős in 1932. Erdős (eventually) proved the existence of such a set using probabilistic methods. This problem asks for a constructive solution. An explicit construction was given by Jain, Pham, Sawhney, and Zakharov [JPSZ24]. The formal statement records the existence of such a set; the linked formal proof exhibits an explicit construction.
- notes: Erdos Problem 29 -- https://www.erdosproblems.com/29
- track: solved
- answer_shape: decide
- source_stem: 29
- mathdb_ref: erdos:29
- source_namespace: Erdos29
- source_theorem: erdos_29
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Asymptotics AdditiveCombinatorics
open scoped Pointwise

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ A : Set ℕ, A + A = Set.univ ∧ ∀ ε : ℝ, 0 < ε →
        (fun n : ℕ => (sumRep A n : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) ^ ε

end Problem
