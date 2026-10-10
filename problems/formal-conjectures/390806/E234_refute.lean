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

- problem_id: E234_refute
- collection: erdos
- question_id: erdos:234
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/234.lean#erdos_234
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that for all `c ≥ 0`, the density `f c` of integers for which `(p (n + 1) - p n) / log n < c` exists and is a continuous function of `c`?
- notes: Erdos Problem 234 -- https://www.erdosproblems.com/234
- track: open
- answer_shape: refute
- pair_id: E234
- pair_role: refute
- source_stem: 234
- mathdb_ref: erdos:234
- source_namespace: Erdos234
- source_theorem: erdos_234
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Real Set
open scoped NNReal

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∃ f : ℝ≥0 → ℝ, Continuous f ∧
          ∀ c : ℝ≥0, HasDensity {n : ℕ | primeGap n / log n < c} (f c)
    )

end Problem
