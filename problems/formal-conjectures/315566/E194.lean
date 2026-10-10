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

- problem_id: E194
- collection: erdos
- question_id: erdos:194
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/194.lean#erdos_194
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k\geq 3$. Must any ordering of $\mathbb{R}$ contain a monotone $k$-term arithmetic progression, that is, some $x_1 <\cdots < x_k$ which forms an increasing or decreasing $k$-term arithmetic progression? The answer is no, even for $k=3$, as shown by Ardal, Brown, and Jungić [ABJ11]. -
- notes: Erdos Problem 194 -- https://www.erdosproblems.com/194
- track: solved
- answer_shape: decide
- source_stem: 194
- mathdb_ref: erdos:194
- source_namespace: Erdos194
- source_theorem: erdos_194
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ k ≥ 3, ∀ r : ℝ → ℝ → Prop, IsStrictTotalOrder ℝ r →
      ∃ s : List ℝ, s.IsAPOfLength k ∧ (s.Pairwise r ∨ s.Pairwise (flip r))

end Problem
