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

- problem_id: E801
- collection: erdos
- question_id: erdos:801
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/801.lean#erdos_801
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $G$ is a graph on $n$ vertices containing no independent set on $>n^{1/2}$ vertices then there is a set of $\leq n^{1/2}$ vertices containing $\gg n^{1/2}\log n$ edges. Proved by Alon [Al96b].
- notes: Erdos Problem 801 -- https://www.erdosproblems.com/801
- track: solved
- answer_shape: decide
- source_stem: 801
- mathdb_ref: erdos:801
- source_namespace: Erdos801
- source_theorem: erdos_801
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter SimpleGraph

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
        ∀ G : SimpleGraph (Fin n), (G.indepNum : ℝ) ≤ √n →
          ∃ S : Finset (Fin n), (S.card : ℝ) ≤ √n ∧
            c * √n * Real.log n ≤ (G.induce (S : Set (Fin n))).edgeSet.ncard

end Problem
