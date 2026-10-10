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

- problem_id: E871
- collection: erdos
- question_id: erdos:871
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/871.lean#erdos_871
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A$ be an additive basis of order $2$, and suppose $1_A\ast 1_A(n)\to \infty$ as $n\to \infty$. Can $A$ be partitioned into two disjoint additive bases of order $2$? A question of Erdős and Nathanson [ErNa88], who proved this is true if $1_A\ast 1_A(n) > c\log n$ (for all large $n$) for some constant $c>(\log\frac{4}{3})^{-1}$. Erdős and Nathanson [ErNa89] also proved that for every $t$ there exists a basis $A$ of order $2$ such that $1_A\ast 1_A(n)\geq t$ for all large $n$ and yet $A$ cannot be partitioned into two disjoint additive bases. This has been disproved by Larsen using Claude Opus 4.5 - in fact only a small modification of the argument of [ErNa89] is required.
- notes: Erdos Problem 871 -- https://www.erdosproblems.com/871
- track: solved
- answer_shape: decide
- source_stem: 871
- mathdb_ref: erdos:871
- source_namespace: Erdos871
- source_theorem: erdos_871
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      ∀ (A : Set ℕ),
        (∀ᶠ n in Filter.atTop, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
        (∀ t, ∀ᶠ n in Filter.atTop, ∃ pairs : Finset (ℕ × ℕ),
          pairs.card ≥ t ∧
            ∀ p ∈ pairs, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2) →
        ∃ (B C : Set ℕ),
          (∀ x, x ∈ A ↔ x ∈ B ∨ x ∈ C) ∧
          Disjoint B C ∧
          (∀ᶠ n in Filter.atTop, ∃ a ∈ B, ∃ b ∈ B, a + b = n) ∧
          (∀ᶠ n in Filter.atTop, ∃ a ∈ C, ∃ b ∈ C, a + b = n)

end Problem
