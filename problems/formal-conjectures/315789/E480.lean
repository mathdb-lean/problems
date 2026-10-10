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

- problem_id: E480
- collection: erdos
- question_id: erdos:480
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/480.lean#erdos_480
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $x_1,x_2,\ldots\in [0,1]$ be an infinite sequence. Is it true that $$\inf_n \liminf_{m\to \infty} n \lvert x_{m+n}-x_m\rvert\leq 5^{-1/2}\approx 0.447?$$ A conjecture of Newman.
- notes: Erdos Problem 480 -- https://www.erdosproblems.com/480
- track: solved
- answer_shape: decide
- source_stem: 480
- mathdb_ref: erdos:480
- source_namespace: Erdos480
- source_theorem: erdos_480
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open Filter

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (x : ℕ → ℝ), (∀ n, x n ∈ Set.Icc 0 1) →
        ⨅ (n : ℕ+), atTop.liminf (fun m => (n : ℕ) * |x (m + (n : ℕ)) - x m|) ≤ 1 / √5

end Problem
