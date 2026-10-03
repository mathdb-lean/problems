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

- problem_id: E873_prove
- collection: erdos
- question_id: erdos:873
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/873.lean#erdos_873
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A = \{a_1 < a_2 < \dots\} \subseteq \mathbb{N}$ and let $F(A,X,k)$ count the number of $i$ such that $[a_i,a_{i+1}, \dots ,a_{i+k−1}] < X$, where the left-hand side is the least common multiple. Is it true that, for every $\epsilon > 0$, there exists some $k$ such that $F(A,X,k) < X^\epsilon$?
- notes: Erdos Problem 873 -- https://www.erdosproblems.com/873
- track: open
- answer_shape: prove
- pair_id: E873
- pair_role: prove
- source_stem: 873
- mathdb_ref: erdos:873
- source_namespace: Erdos873
- source_theorem: erdos_873
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Let $a$ be some sequence of natural numbers. We set $F(A,X,k)$ to be the count of
the number of $i$ such that $[a_i,a_{i+1}, \dots ,a_{i+k−1}] < X$,
where the left-hand side is the least common multiple. -/
noncomputable abbrev F (a : ℕ → ℕ) (X : ℝ) (k : ℕ) : ℕ∞ :=
  {i : ℕ | (Finset.range k).lcm (fun m => a (i + m)) < X}.encard

abbrev Target : Prop :=
    ∀ᵉ (a : ℕ → ℕ) (ε > (0 : ℝ)), 0 < a 0 → StrictMono a →
        ∃ k, ∀ X > 0, F a X k < (X^ε).toEReal

end Problem
