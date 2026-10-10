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

- problem_id: E243
- collection: erdos
- question_id: erdos:243
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/243.lean#erdos_243
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $a_1 < a_2 < \dots$ be a sequence of integers such that $\lim_{n\to\infty} \frac{a_n}{a_{n-1}^2} = 1$ and $\sum \frac{1}{a_n} \in \mathbb{Q}$. Then, for all sufficiently large $n \ge 1$, $a_n = a_{n-1}^2 - a_{n-1} + 1$.
- notes: Erdos Problem 243 -- https://www.erdosproblems.com/243
- track: open
- answer_shape: proof
- source_stem: 243
- mathdb_ref: erdos:243
- source_namespace: Erdos243
- source_theorem: erdos_243
- source_category: research open
- source_ams: 40
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

open scoped Topology

namespace Problem

abbrev Target : Prop :=
    ∀ (a : ℕ → ℕ) (ha₀ : StrictMono a)
        (ha₁ : Tendsto (fun n ↦ (a n : ℝ) / a (n - 1) ^ 2) atTop (𝓝 1))
        (ha₂ : Summable ((1 : ℚ) / a ·)),
      ∀ᶠ n in atTop, a n = a (n - 1) ^ 2 - a (n - 1) + 1

end Problem
