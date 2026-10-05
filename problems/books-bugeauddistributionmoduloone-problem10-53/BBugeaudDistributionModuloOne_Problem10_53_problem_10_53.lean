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

- problem_id: BBugeaudDistributionModuloOne_Problem10_53_problem_10_53
- collection: books
- question_id: books:BugeaudDistributionModuloOne/Problem10_53
- source: formal-conjectures
- source_locator: FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_53.lean#problem_10_53
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Problem 10.53. There is an irrational real number $\xi$ such that $E(\xi) < \log 2$ and $E(\xi, b) < \log b$ for some integer $b \ge 2$. Answered by Temur [Tem26].
- notes: Book problem BugeaudDistributionModuloOne/Problem10_53 -- https://arxiv.org/abs/2609.16362
- track: solved
- answer_shape: proof
- source_stem: BugeaudDistributionModuloOne/Problem10_53
- source_namespace: Bugeaud53
- source_theorem: problem_10_53
- source_category: research solved
- source_ams: 11 37
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Real

abbrev Target : Prop :=
    ∃ ξ : ℝ, Irrational ξ ∧ cfEntropy ξ < (Real.log 2 : EReal) ∧
      ∃ b : ℕ, 2 ≤ b ∧ baseEntropy b ξ < (Real.log b : EReal)

end Problem
