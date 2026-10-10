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

- problem_id: E159
- collection: erdos
- question_id: erdos:159
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/159.lean#erdos_159
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: There exists some constant $c>0$ such that $$R(C_4,K_n) \ll n^{2-c}.$$ The prize of $100 is offered in [Er78] for a proof or disproof. This problem is #17 in Ramsey Theory in the graphs problem collection.
- notes: Erdos Problem 159 -- https://www.erdosproblems.com/159
- track: open
- answer_shape: proof
- source_stem: 159
- mathdb_ref: erdos:159
- source_namespace: Erdos159
- source_theorem: erdos_159
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∃ (c : ℝ) (_ : 0 < c) (C : ℝ),
      ∀ (n : ℕ), 1 ≤ n →
        (SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
          (SimpleGraph.completeGraph (Fin n)) : ℝ) ≤ C * (n : ℝ) ^ (2 - c)

end Problem
