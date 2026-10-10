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

- problem_id: BBugeaudDistributionModuloOne_Problem10_8_problem_10_8
- collection: books
- question_id: books:BugeaudDistributionModuloOne/Problem10_8
- source: formal-conjectures
- source_locator: FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_8.lean#problem_10_8
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Problem 10.8 ($p$-adic Littlewood conjecture). For every real number $\xi$ and every prime number $p$, $$\inf_{q \ge 1} q \cdot \lVert q \xi \rVert \cdot |q|_p = 0,$$ where $\lVert \cdot \rVert$ denotes the distance to the nearest integer and $|\cdot|_p$ denotes the $p$-adic absolute value. Posed by de Mathan and Teulié [dMT04].
- notes: Book problem BugeaudDistributionModuloOne/Problem10_8
- track: open
- answer_shape: proof
- source_stem: BugeaudDistributionModuloOne/Problem10_8
- source_namespace: Bugeaud08
- source_theorem: problem_10_8
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∀ (ξ : ℝ) (p : ℕ) (hp : p.Prime),
      sInf {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
        x = q * padicNorm p q * distToNearestInt (q * ξ)} = 0

end Problem
