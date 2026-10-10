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

- problem_id: E268
- collection: erdos
- question_id: erdos:268
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/268.lean#erdos_268
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let `X` be the set of points in `Fin d → ℝ` of the shape `fun i : Fin d => ∑' n : A, (1 : ℝ) / (n + i)` for some infinite subset `A ⊆ ℕ` such that `1 / n` is summable over `A`. `X` has nonempty interior. This is proved in [KoTa24]. -
- notes: Erdos Problem 268 -- https://www.erdosproblems.com/268
- track: solved
- answer_shape: proof
- source_stem: 268
- mathdb_ref: erdos:268
- source_namespace: Erdos268
- source_theorem: erdos_268
- source_category: research solved
- source_ams: 40 54
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∀ (d : ℕ),
      (interior {x : Fin d → ℝ | ∃ A : Set ℕ, A.Infinite ∧
          Summable (fun n : A => (1 : ℝ) / n ) ∧
          x = fun i : Fin d => ∑' n : A, (1 : ℝ) / (n + i)}).Nonempty

end Problem
