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

- problem_id: E495_refute
- collection: erdos
- question_id: erdos:495
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/495.lean#erdos_495
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\alpha,\beta \in \mathbb{R}$. Is it true that$$\liminf_{n\to \infty} n \| n\alpha \| \| n\beta\| =0$$? This is also known as the Littlewood conjecture.
- notes: Erdos Problem 495 -- https://www.erdosproblems.com/495
- track: open
- answer_shape: refute
- pair_id: E495
- pair_role: refute
- source_stem: 495
- mathdb_ref: erdos:495
- source_namespace: Erdos495
- source_theorem: erdos_495
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∀ α β : ℝ, liminf (fun n : ℕ ↦ (n : ℝ) * distToNearestInt (n * α)
        * distToNearestInt (n * β)) atTop = 0
    )

end Problem
