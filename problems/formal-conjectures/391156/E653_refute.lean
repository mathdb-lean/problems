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

- problem_id: E653_refute
- collection: erdos
- question_id: erdos:653
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/653.lean#erdos_653
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $x_1,\ldots,x_n\in \mathbb{R}^2$ and let $R(x_i)=\#\{ \lvert x_j-x_i\rvert : j\neq i\}$, where the points are ordered such that $$R(x_1)\leq \cdots \leq R(x_n).$$ Let $g(n)$ be the maximum number of distinct values the $R(x_i)$ can take. Is it true that $g(n) \geq (1-o(1))n$?
- notes: Erdos Problem 653 -- https://www.erdosproblems.com/653
- track: open
- answer_shape: refute
- pair_id: E653
- pair_role: refute
- source_stem: 653
- mathdb_ref: erdos:653
- source_namespace: Erdos653
- source_theorem: erdos_653
- source_category: research open
- source_ams: 5 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Finset EuclideanGeometry Filter

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
          ∀ᶠ n in atTop, (1 - o n) * n ≤ maximalDistinctDistancesFrom n
    )

end Problem
