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

- problem_id: E12_parts_ii
- collection: erdos
- question_id: erdos:12
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/12.lean#erdos_12.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A$ be an infinite set such that there are no distinct $a,b,c \in A$ such that $a \mid (b+c)$ and $b,c > a$. Does there exist some absolute constant $c > 0$ such that there are always infinitely many $N$ with $|A \cap \{1, \dotsc, N\}| < N^{1−c}$? The DeepMind prover agent has found a formal disproof of this statement.
- notes: Erdos Problem 12 -- https://www.erdosproblems.com/12
- track: solved
- answer_shape: decide
- source_stem: 12
- mathdb_ref: erdos:12
- source_namespace: Erdos12
- source_theorem: erdos_12.parts.ii
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Set

namespace Problem

/--
A set `A` is "good" if it is infinite and there are no distinct `a,b,c` in `A`
such that `a ∣ (b+c)` and `b > a`, `c > a`.
-/
abbrev IsGood (A : Set ℕ) : Prop := A.Infinite ∧
  ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A), a ∣ b + c → a < b →
  a < c → b = c


abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ c > (0 : ℝ), ∀ (A : Set ℕ), IsGood A →
        {N : ℕ| (A ∩ Icc 1 N).ncard < (N : ℝ) ^ (1 - c)}.Infinite

end Problem
