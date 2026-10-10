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

- problem_id: E60
- collection: erdos
- question_id: erdos:60
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/60.lean#erdos_60
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does every graph on $n$ vertices with $>\mathrm{ex}(n;C_4)$ edges contain $\gg n^{1/2}$ many copies of $C_4$?
- notes: Erdos Problem 60 -- https://www.erdosproblems.com/60
- track: open
- answer_shape: proof
- source_stem: 60
- mathdb_ref: erdos:60
- source_namespace: Erdos60
- source_theorem: erdos_60
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph Filter
open scoped Real

abbrev Target : Prop :=
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (extremalNumber n (cycleGraph 4) < G.edgeFinset.card) →
          (c * Real.sqrt (n : ℝ) ≤ ({ H' : G.Subgraph | Nonempty (H'.coe ≃g cycleGraph 4) }.ncard : ℝ))

end Problem
