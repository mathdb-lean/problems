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

- problem_id: E1008
- collection: erdos
- question_id: erdos:1008
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1008.lean#erdos_1008
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does every graph with $m$ edges contain a subgraph with $\gg m^{2/3}$ edges which contains no $C_4$? This problem was first solved in the affirmative by Conlon, Fox, and Sudakov [CFS14b]. A simple proof is given by Hunter in the comments.
- notes: Erdos Problem 1008 -- https://www.erdosproblems.com/1008
- track: solved
- answer_shape: decide
- source_stem: 1008
- mathdb_ref: erdos:1008
- source_namespace: Erdos1008
- source_theorem: erdos_1008
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open SimpleGraph

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
          ∃ H ≤ G, (cycleGraph 4).Free H ∧
            c * (G.edgeSet.ncard : ℝ) ^ (2 / 3 : ℝ) ≤ (H.edgeSet.ncard : ℝ)

end Problem
