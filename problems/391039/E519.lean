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

- problem_id: E519
- collection: erdos
- question_id: erdos:519
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/519.lean#erdos_519
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $z_1,\ldots,z_n\in \mathbb{C}$ with $z_1=1$. Must there exist an absolute constant $c>0$ such that $$ \max_{1\leq k\leq n}\left\lvert \sum_{i}z_i^k\right\rvert>c? $$ Atkinson proved that $c=1/6$ suffices.
- notes: Erdos Problem 519 -- https://www.erdosproblems.com/519
- track: solved
- answer_shape: decide
- source_stem: 519
- mathdb_ref: erdos:519
- source_namespace: Erdos519
- source_theorem: erdos_519
- source_category: research solved
- source_ams: 30
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open scoped BigOperators

namespace Problem

/-- The $k$th power sum of a finite sequence of complex numbers. -/
noncomputable def powerSum {n : ℕ} (z : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ i : Fin n, z i ^ k

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ c : ℝ, 0 < c ∧
          ∀ (n : ℕ) (hn : 0 < n) (z : Fin n → ℂ),
            z ⟨0, hn⟩ = 1 →
              ∃ k : Fin n, c < ‖powerSum z (k.val + 1)‖

end Problem
