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

- problem_id: E1210_prove
- collection: erdos
- question_id: erdos:1210
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1210.lean#erdos_1210
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq [1,n)$ be a set of integers such that $(a,b)=1$ for all distinct $a,b\in A$. Is it true that $\sum_{a\in A}\frac{1}{n-a}\leq \sum_{p < n}\frac{1}{p}+O(1)$?
- notes: Erdos Problem 1210 -- https://www.erdosproblems.com/1210
- track: open
- answer_shape: prove
- pair_id: E1210
- pair_role: prove
- source_stem: 1210
- mathdb_ref: erdos:1210
- source_namespace: Erdos1210
- source_theorem: erdos_1210
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Finset

namespace Problem

abbrev Target : Prop :=
    ∃ C : ℝ, ∀ n : ℕ, ∀ A : Finset ℕ,
        (∀ a ∈ A, 1 ≤ a ∧ a < n) →
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → a.Coprime b) →
        ∑ a ∈ A, (1 / ((n : ℝ) - a)) ≤ (∑ p ∈ (range n).filter Prime, (1 / (p : ℝ))) + C

end Problem
