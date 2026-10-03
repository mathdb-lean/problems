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

- problem_id: E586
- collection: erdos
- question_id: erdos:586
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/586.lean#erdos_586
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a covering system such that no two of the moduli divide each other? Asked by Schinzel, motivated by a question of Erdős and Selfridge (see [7](https://www.erdosproblems.com/7)). The answer is no, as proved by Balister, Bollobás, Morris, Sahasrabudhe, and Tiba [BBMST22]. The moduli of a `CoveringSystem ℤ` are the ideals $(m_i)$; the modulus $m_i$ divides $m_j$ exactly when $(m_j)\subseteq (m_i)$.
- notes: Erdos Problem 586 -- https://www.erdosproblems.com/586
- track: solved
- answer_shape: decide
- source_stem: 586
- mathdb_ref: erdos:586
- source_namespace: Erdos586
- source_theorem: erdos_586
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ c : CoveringSystem ℤ, Pairwise fun i j ↦ ¬ c.moduli j ≤ c.moduli i

end Problem
