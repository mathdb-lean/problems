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

- problem_id: E817_prove
- collection: erdos
- question_id: erdos:817
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/817.lean#erdos_817
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k \geq 3$. Define $g_k(n)$ to be the minimal $N$ such that $\{1, ..., N\}$ contains some $A$ of size $|A| = n$ such that $$ \langle A\rangle = \left\{\sum_{a \in A} \epsilon_a a : \epsilon_a \in\{0, 1\}\right\} $$ contains no non-trivial $k$-term arithmetic progression. Estimate $g_k(n)$. In particular, is it true that $$ g_3(n) \gg 3^n $$
- notes: Erdos Problem 817 -- https://www.erdosproblems.com/817
- track: open
- answer_shape: prove
- pair_id: E817
- pair_role: prove
- source_stem: 817
- mathdb_ref: erdos:817
- source_namespace: Erdos817
- source_theorem: erdos_817
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

/-- Define $g_k(n)$ to be the minimal $N$ such that $\{1, ..., N\}$ contains some $A$ of
size $|A| = n$ such that
$$
  \langle A\rangle = \left\{\sum_{a \in A} \epsilon_a a : \epsilon_a \in\{0, 1\}\right\}
$$
contains no non-trivial $k$-term arithmetic progression. -/
noncomputable
def g (k : ℕ) (n : ℕ) : ℕ := sInf { N | ∃ A ⊆ Finset.Icc 1 N, A.card = n ∧
    ∀ s, s ⊆ { ∑ a ∈ B, a | B ∈ A.powerset } → s.IsAPOfLengthFree k}

abbrev Target : Prop :=
    (fun n => (3 ^ n : ℝ)) =O[atTop] fun n => (g 3 n : ℝ)

end Problem

-- Formalisation note : only formalising the "In particular" part
