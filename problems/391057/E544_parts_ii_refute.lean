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

- problem_id: E544_parts_ii_refute
- collection: erdos
- question_id: erdos:544
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/544.lean#erdos_544.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Similarly, prove or disprove that $$R(3,k+1)-R(3,k)=o(k).$$
- notes: Erdos Problem 544 -- https://www.erdosproblems.com/544
- track: open
- answer_shape: refute
- pair_id: E544_parts_ii
- pair_role: refute
- source_stem: 544
- mathdb_ref: erdos:544
- source_namespace: Erdos544
- source_theorem: erdos_544.parts.ii
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

abbrev Target : Prop :=
    ¬ (
      (fun k : ℕ ↦ (SimpleGraph.classicalRamsey 3 (k + 1) : ℝ) -
            (SimpleGraph.classicalRamsey 3 k : ℝ)) =o[atTop] (fun k : ℕ ↦ (k : ℝ))
    )

end Problem
