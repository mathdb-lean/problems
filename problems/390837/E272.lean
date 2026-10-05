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

- problem_id: E272
- collection: erdos
- question_id: erdos:272
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/272.lean#erdos_272
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $N\geq 1$. What is the largest $t$ such that there are $A_1,\ldots,A_t\subseteq \{1,\ldots,N\}$ with $A_i\cap A_j$ a non-empty arithmetic progression for all $i\neq j$?
- notes: Erdos Problem 272 -- https://www.erdosproblems.com/272
- track: open
- answer_shape: value
- answer_type: ℕ → ℕ
- answer_pinned: false
- answer_pinned_reason: closable_by_rfl
- source_stem: 272
- mathdb_ref: erdos:272
- source_namespace: Erdos272
- source_theorem: erdos_272
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Asymptotics Finset

namespace Problem

/-- Let $N \in\mathbb{N}$. We say that $\{A_1, ..., A_t\}\subseteq
\mathcal{P}(\{1, \dots, N\})$ is an arithmetic intersection set if
$A_i \cap A_j$ is a non-empty arithmetic progression for each $i \neq j$.
-/
def IsArithInterSet (N : ℕ) (A : Finset (Finset ℕ)) : Prop :=
  A ⊆ (Finset.Icc 1 N).powerset ∧
    (SetLike.coe A).Pairwise fun S T ↦ ∃ l > 0, (SetLike.coe (S ∩ T)).IsAPOfLength l

/-- For each $N > 0$, let $t$ be the largest size of an arithmetic
intersection set. -/
noncomputable def maxArithInterCard (N : ℕ) : ℕ :=
  sSup {#A | (A : _) (_ : IsArithInterSet N A)}

abbrev Target (value : ℕ → ℕ) : Prop :=
    ∀ N ≥ 1, maxArithInterCard N = value N

end Problem
