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

- problem_id: E247_prove
- collection: erdos
- question_id: erdos:247
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/247.lean#erdos_247
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $n_1 < n_2 < \cdots$ be a sequence of integers such that $$ \limsup \frac{n_k}{k} = \infty. $$ Is $$ \sum_{k=1}^{\infty} \frac{1}{2^{n_k}} $$ transcendental?
- notes: Erdos Problem 247 -- https://www.erdosproblems.com/247
- track: open
- answer_shape: prove
- pair_id: E247
- pair_role: prove
- source_stem: 247
- mathdb_ref: erdos:247
- source_namespace: Erdos247
- source_theorem: erdos_247
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

abbrev Target : Prop :=
    ∀ (n : ℕ → ℕ), (StrictMono n) →
        atTop.limsup (fun k => (n k / k.succ : EReal)) = ⊤ →
        Transcendental ℚ (∑' k, (1 : ℝ) / 2 ^ n k)

end Problem
