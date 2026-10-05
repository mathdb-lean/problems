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

- problem_id: E424
- collection: erdos
- question_id: erdos:424
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/424.lean#erdos_424
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $a_1 = 2$ and $a_2 = 3$ and continue the sequence by appending to $a_1, \ldots, a_n$ all possible values of $a_i a_j - 1$ with $i \neq j$. Is it true that the set of integers which eventually appear has positive density? As explained on [erdosproblems.com/424](https://www.erdosproblems.com/424), "positive density" here means positive *lower* density: is there $c > 0$ such that for all large $x$ at least $cx$ of the integers in $[1, x]$ appear? See `erdos_424.variants.exact_density` for the literal reading. The answer is yes: Korsky [Ko26] (with ChatGPT 5.6 Pro) proved that the set has positive lower density. The linked formal proof (Alexeev and Codex) shows that there is `c > 0` with `c * x ≤ #{n ∈ [1, x] | n ∈ generatedSet}` for all large `x`, which gives `c / 2 ≤ generatedSet.lowerDensity`.
- notes: Erdos Problem 424 -- https://www.erdosproblems.com/424
- track: solved
- answer_shape: decide
- source_stem: 424
- mathdb_ref: erdos:424
- source_namespace: Erdos424
- source_theorem: erdos_424
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open Set

/--
Defines the set of new numbers generated from a set A by the operation
$x y - 1$ for $x \neq y$.
-/
def nextGeneration (A : Set ℕ) : Set ℕ :=
  { z : ℕ | ∃ x y, x ∈ A ∧ y ∈ A ∧ x ≠ y ∧ z = x * y - 1 }

/--
The sequence of sets $A_n$ where $A_0 = \{2, 3\}$ and $A_{n+1}$ is $A_n$ union all newly
generated elements.
-/
def sequenceSet : ℕ → Set ℕ
  | 0 => {2, 3}
  | n + 1 => (sequenceSet n) ∪ (nextGeneration (sequenceSet n))

/-- The set of integers which eventually appear in the sequence, which is the union of all $A_n$. -/
def generatedSet : Set ℕ := ⋃ n : ℕ, sequenceSet n

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ 0 < generatedSet.lowerDensity

end Problem
