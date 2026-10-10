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

- problem_id: E410_prove
- collection: erdos
- question_id: erdos:410
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/410.lean#erdos_410
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $σ_1(n) = σ(n)$, the sum of divisors function, and $σ_k(n) = σ(σ_{k-1}(n))$. Is it true that $\lim_{k → ∞} σ_k(n)^{\frac 1 k} = ∞$? This is problem (iii) from Erdos, Granville, Pomerance, Spiro "On the normal behavior of the iterates of some arithmetical functions" (page 169 of the book "Analytic Number Theory", 1990).
- notes: Erdos Problem 410 -- https://www.erdosproblems.com/410
- track: open
- answer_shape: prove
- pair_id: E410
- pair_role: prove
- source_stem: 410
- mathdb_ref: erdos:410
- source_namespace: Erdos410
- source_theorem: erdos_410
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open ArithmeticFunction Filter

namespace Problem

abbrev Target : Prop :=
    ∀ n > 1,
        Tendsto (fun k : ℕ ↦ ((sigma 1)^[k] n : ℝ) ^ (1 / (k : ℝ))) atTop atTop

end Problem
