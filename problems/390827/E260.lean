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

- problem_id: E260
- collection: erdos
- question_id: erdos:260
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/260.lean#erdos_260
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $a_1 < a_2 < \cdots$ be an increasing sequence such that $\frac{a_n}{n} \to \infty$. Is the sum $\sum_{n}^{\infty} \frac{a_n}{2^{a_n}}$ irrational? For a proof, see [Wang, *Sparse Polynomial-Weighted Expansions*] (https://arxiv.org/abs/2606.24972).
- notes: Erdos Problem 260 -- https://www.erdosproblems.com/260
- track: solved
- answer_shape: decide
- source_stem: 260
- mathdb_ref: erdos:260
- source_namespace: Erdos260
- source_theorem: erdos_260
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
    verdict ↔
                      ∀ a : ℕ → ℤ, ∀ s : ℝ,
                      StrictMono a →
                      Tendsto (fun n => (a n : ℝ ) / n ) atTop atTop →
                      HasSum (fun n => (a n : ℝ ) / 2 ^ a n) s → Irrational s

end Problem
