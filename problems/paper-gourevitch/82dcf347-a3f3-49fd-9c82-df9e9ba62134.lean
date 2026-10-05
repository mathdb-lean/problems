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

- problem_id: RGourevitch_gourevitch_series_identity
- collection: paper
- question_id: paper:Gourevitch
- source: formal-conjectures
- source_locator: FormalConjectures/Paper/Gourevitch.lean#gourevitch_series_identity
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The Gourevitch series identity: The following identity holds: $\sum_{n=0}^{\infty} \frac{1 + 14 n + 76 n^2 + 168 n^3}{2^{20 n}} \binom{2n}{n}^7 = \frac{32}{\pi^3}.$ This was originally conjectured in [G2003] by Guillera and proven in [A2025] by Au.
- notes: Problem from Gourevitch -- https://doi.org/10.1080/10586458.2003.10504518
- track: solved
- answer_shape: proof
- source_stem: Gourevitch
- source_namespace: Gourevitch
- source_theorem: gourevitch_series_identity
- source_category: research solved
- source_ams: 11 33
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∑' n : ℕ, ((1 + 14 * n + 76 * n ^ 2 + 168 * n ^ 3) / (2 ^ (20 * n)) : ℝ)
      * Nat.centralBinom n ^ 7 = 32 / (Real.pi ^ 3)

end Problem
