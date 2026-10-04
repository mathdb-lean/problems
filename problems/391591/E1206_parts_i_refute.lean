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

- problem_id: E1206_parts_i_refute
- collection: erdos
- question_id: erdos:1206
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1206.lean#erdos_1206.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does $\{1,2^3,\ldots,N^3\}$ contain a Sidon set of size $\gg N$?
- notes: Erdos Problem 1206 -- https://www.erdosproblems.com/1206
- track: open
- answer_shape: refute
- pair_id: E1206_parts_i
- pair_role: refute
- source_stem: 1206
- mathdb_ref: erdos:1206
- source_namespace: Erdos1206
- source_theorem: erdos_1206.parts.i
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ N in Filter.atTop, ∃ S : Finset ℕ,
            S ⊆ (Finset.Icc 1 N).image (fun n => n ^ 3) ∧
            IsSidon (S : Set ℕ) ∧ c * (N : ℝ) ≤ (S.card : ℝ)
    )

end Problem
