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

- problem_id: E862_parts_ii
- collection: erdos
- question_id: erdos:862
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/862.lean#erdos_862.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A_1(N)$ be the number of maximal Sidon subsets of $\{1,\ldots,N\}$. Is it true that $$A_1(N) > 2^{N^c}$$ for some constant $c>0$? A problem of Cameron and Erdős. This is resolved as a consequence of results of Saxton and Thomason [SaTh15] - they prove that the number of Sidon sets in $\{1,\ldots,N\}$ is at least $2^{(1.16+o(1))N^{1/2}}$. Since each Sidon set is contained in a maximal Sidon set, and each maximal Sidon set contains at most $2^{(1+o(1))N^{1/2}}$ Sidon sets, it follows that $$A_1(N) \geq 2^{(0.16+o(1))N^{1/2}}.$$
- notes: Erdos Problem 862 -- https://www.erdosproblems.com/862
- track: solved
- answer_shape: decide
- source_stem: 862
- mathdb_ref: erdos:862
- source_namespace: Erdos862
- source_theorem: erdos_862.parts.ii
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Finset Filter

namespace Problem

/--
$A_1(N)$, the number of maximal Sidon subsets of $\{1, \dots, N\}$.
-/
noncomputable def numMaximalSidonSets (N : ℕ) : ℕ :=
  {A : Finset ℕ | A ⊆ Icc 1 N ∧ Set.IsMaximalSidonSetIn (A : Set ℕ) N}.ncard

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
          (2 : ℝ) ^ ((N : ℝ) ^ c) < (numMaximalSidonSets N : ℝ)

end Problem
