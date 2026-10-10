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

- problem_id: E542_parts_ii
- collection: erdos
- question_id: erdos:542
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/542.lean#erdos_542.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that if $A\subseteq\{2,\ldots,n\}$ is a set such that $[a,b]>n$ for all $a\neq b$, then there must be $\gg n$ many $m\leq n$ which are not divisible by any $a\in A$? The answer is no, proved by Schinzel and Szekeres [ScSz59]. The element $1$ is excluded: $A=\{1\}$ satisfies the hypothesis and leaves no such $m$, so without this restriction the answer would be negative for a trivial reason.
- notes: Erdos Problem 542 -- https://www.erdosproblems.com/542
- track: solved
- answer_shape: decide
- source_stem: 542
- mathdb_ref: erdos:542
- source_namespace: Erdos542
- source_theorem: erdos_542.parts.ii
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Real

namespace Problem

/-- A set `A ⊆ {1, …, n}` such that `lcm(a, b) > n` for all distinct `a, b ∈ A`. -/
def IsLcmFree (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧ (A : Set ℕ).Pairwise fun a b ↦ n < Nat.lcm a b

/-- The integers `1 ≤ m ≤ n` which are not divisible by any element of `A`. -/
def uncovered (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun m ↦ ∀ a ∈ A, ¬ a ∣ m

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ c > 0, ∀ (n : ℕ) (A : Finset ℕ), IsLcmFree n A → 1 ∉ A →
          c * n ≤ ((uncovered n A).card : ℝ)

end Problem
