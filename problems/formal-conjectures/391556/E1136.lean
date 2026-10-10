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

- problem_id: E1136
- collection: erdos
- question_id: erdos:1136
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1136.lean#erdos_1136
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does there exist $A\subset \mathbb{N}$ with lower density $>1/3$ such that $a+b\neq 2^k$ for any $a,b\in A$ and $k\geq 0$? Müller [Mu11] settled this question in the affirmative: in fact one can take $A$ to be the set of all integers congruent to $3\cdot 2^i\pmod{2^{i+2}}$ for any $i\geq 0$, which has density $1/2$.
- notes: Erdos Problem 1136 -- https://www.erdosproblems.com/1136
- track: solved
- answer_shape: decide
- source_stem: 1136
- mathdb_ref: erdos:1136
- source_namespace: Erdos1136
- source_theorem: erdos_1136
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/--
A set `A` of natural numbers has the property in the question if `a + b ≠ 2 ^ k` for all
`a, b ∈ A` (not necessarily distinct) and all `k ≥ 0`.
-/
def AvoidsPowersOfTwo (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ k : ℕ, a + b ≠ 2 ^ k

/-- The set of all integers congruent to $3\cdot 2^i\pmod{2^{i+2}}$ for some $i\geq 0$. -/
def muellerSet : Set ℕ := {n | ∃ i : ℕ, n ≡ 3 * 2 ^ i [MOD 2 ^ (i + 2)]}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ A : Set ℕ, (1 / 3 : ℝ) < A.lowerDensity ∧ AvoidsPowersOfTwo A

end Problem
