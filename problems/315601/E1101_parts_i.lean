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

- problem_id: E1101_parts_i
- collection: erdos
- question_id: erdos:1101
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1101.lean#erdos_1101.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: 1. There is NO good sequence with polynomial growth.
- notes: Erdos Problem 1101 -- https://www.erdosproblems.com/1101
- track: open
- answer_shape: proof
- source_stem: 1101
- mathdb_ref: erdos:1101
- source_namespace: Erdos1101
- source_theorem: erdos_1101.parts.i
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat Filter

namespace Problem

/-- The set of integers not divisible by any u_i. -/
def ASet (u : ℕ → ℕ) : Set ℕ :=
  { a | ∀ i, ¬ u i ∣ a }

/-- The sequence of integers A_u which are not divisible by any u_i
arranged in a monotonic sequence. -/
noncomputable def A (u : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.nth (fun a => a ∈ ASet u) n

/-- t_x such that u_0 ... u_{t_x-1} ≤ x < u_0 ... u_{t_x}.
-/
noncomputable def t (u : ℕ → ℕ) (x : ℕ) : ℕ :=
  sSup { k | ∏ i ∈ Finset.range k, u i ≤ x }

/-- A sequence is "good" if
1. it is strictly monotone
2. it is pairwise coprime
3. the sum of reciprocals converges
4. the gap between consecutive elements in A(u) is bounded relative to t_x. -/
def IsGood (u : ℕ → ℕ) : Prop :=
  StrictMono u ∧
  (∀ i j, i ≠ j → Coprime (u i) (u j)) ∧
  Summable (fun n => 1 / (u n : ℝ)) ∧
  ∀ ε > 0, ∀ᶠ x in atTop,
    ∀ k, A u k < x →
      (A u (k + 1) : ℝ) - A u k < (1 + ε) * (t u x : ℝ) * (∏' i : ℕ, (1 - 1 / (u i : ℝ)))⁻¹

abbrev Target : Prop :=
    ¬ ∃ u, IsGood u ∧ ∃ k : ℕ, (fun n => (u n : ℝ)) =O[atTop] (fun n => (n : ℝ) ^ k)

end Problem
