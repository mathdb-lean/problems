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

- problem_id: E39_prove
- collection: erdos
- question_id: erdos:39
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/39.lean#erdos_39
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there an infinite Sidon set $A\subset \mathbb{N}$ such that $\lvert A\cap \{1\ldots,N\}\rvert \gg_\epsilon N^{1/2-\epsilon}$ for all $\varepsilon > 0$?
- notes: Erdos Problem 39 -- https://www.erdosproblems.com/39
- track: open
- answer_shape: prove
- pair_id: E39
- pair_role: prove
- source_stem: 39
- mathdb_ref: erdos:39
- source_namespace: Erdos39
- source_theorem: erdos_39
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter

abbrev Target : Prop :=
    ∃ (A : Set ℕ), A.Infinite ∧ IsSidon A ∧
        ∀ᵉ  (ε  > (0 : ℝ)),
        (· ^ (1 / 2 - ε) : ℕ → ℝ) =O[atTop] fun N => (((Set.Icc 1 N) ∩ A).ncard : ℝ)

end Problem
