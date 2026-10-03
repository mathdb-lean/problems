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

- problem_id: E281
- collection: erdos
- question_id: erdos:281
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/281.lean#erdos_281
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $n_1<n_2<\cdots$ be an infinite sequence such that, for any choice of congruence classes $a_i\pmod{n_i}$, the set of integers not satisfying any of the congruences $a_i\pmod{n_i}$ has density $0$. Is it true that for every $\epsilon>0$ there exists some $k$ such that, for every choice of congruence classes $a_i$, the density of integers not satisfying any of the congruences $a_i\pmod{n_i}$ for $1\leq i\leq k$ is less than $\epsilon$? The answer is yes; the linked Lean proof formalizes Somani's argument.
- notes: Erdos Problem 281 -- https://www.erdosproblems.com/281
- track: solved
- answer_shape: decide
- source_stem: 281
- mathdb_ref: erdos:281
- source_namespace: Erdos281
- source_theorem: erdos_281
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Topology

namespace Problem

/-- Choices of congruence classes $a_i \pmod{n_i}$. -/
def ResidueChoice (n : ℕ → ℕ) := ∀ i : ℕ, ZMod (n i)

/-- The integers avoiding all congruences $a_i \pmod{n_i}$. -/
def avoidAll (n : ℕ → ℕ) (a : ResidueChoice n) : Set ℤ :=
  {m | ∀ i : ℕ, (m : ZMod (n i)) ≠ a i}

/-- The integers avoiding the first $k$ congruences $a_i \pmod{n_i}$. -/
def avoidPrefix (n : ℕ → ℕ) (a : ResidueChoice n) (k : ℕ) : Set ℤ :=
  {m | ∀ i : ℕ, i < k → (m : ZMod (n i)) ≠ a i}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (n : ℕ → ℕ), StrictMono n → (∀ i, 0 < n i) →
          (∀ a : ResidueChoice n, Set.HasIntDensity (avoidAll n a) 0) →
            ∀ ε : ℝ, 0 < ε →
              ∃ k : ℕ, ∀ a : ResidueChoice n,
                ∃ d : ℝ, Set.HasIntDensity (avoidPrefix n a k) d ∧ d < ε

end Problem
