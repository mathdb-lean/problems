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

- problem_id: E1150_prove
- collection: erdos
- question_id: erdos:1150
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1150.lean#erdos_1150
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there some constant $c > 0$ such that, for all large enough $n$ and all polynomials $P$ of degree $n$ with coefficients in $\{-1, 1\}$, $$\max_{|z|=1} |P(z)| > (1 + c) \sqrt{n}?$$
- notes: Erdos Problem 1150 -- https://www.erdosproblems.com/1150
- track: open
- answer_shape: prove
- pair_id: E1150
- pair_role: prove
- source_stem: 1150
- mathdb_ref: erdos:1150
- source_namespace: Erdos1150
- source_theorem: erdos_1150
- source_category: research open
- source_ams: 12 30
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Polynomial

namespace Problem

abbrev Target : Prop :=
    ∃ c > 0, ∀ᶠ n in Filter.atTop,
      ∀ P : ℂ[X],  (∀ i ≤ P.natDegree, P.coeff i = - 1 ∨ P.coeff i = 1) → P.natDegree = n →
        ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ > (1 + c) * Real.sqrt n

end Problem
