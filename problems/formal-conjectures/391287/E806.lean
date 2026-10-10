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

- problem_id: E806
- collection: erdos
- question_id: erdos:806
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/806.lean#erdos_806
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq \{1,\ldots,n\}$ with $\lvert A\rvert \leq n^{1/2}$. Must there exist some $B\subset\mathbb{Z}$ with $\lvert B\rvert=o(n^{1/2})$ such that $A\subseteq B+B$? A problem of Erdős and Newman [ErNe77], who proved that there exist $A$ with $\lvert A\rvert\asymp n^{1/2}$ such that if $A\subseteq B+B$ then $$\lvert B\rvert \gg \frac{\log\log n}{\log n}n^{1/2}.$$ Resolved by Alon, Bukh, and Sudakov [ABS09], who proved that for any $A\subseteq \{1,\ldots,n\}$ with $\lvert A\rvert \leq n^{1/2}$ there exists some $B$ such that $A\subseteq B+B$ and $$\lvert B\rvert \ll \frac{\log\log n}{\log n}n^{1/2}.$$ See also [333](https://www.erdosproblems.com/333).
- notes: Erdos Problem 806 -- https://www.erdosproblems.com/806
- track: solved
- answer_shape: decide
- source_stem: 806
- mathdb_ref: erdos:806
- source_namespace: Erdos806
- source_theorem: erdos_806
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter
open scoped Pointwise

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → (A.card : ℝ) ≤ √n →
          ∃ B : Finset ℤ, A.map Nat.castEmbedding ⊆ B + B ∧ (B.card : ℝ) ≤ ε * √n

end Problem
