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

- problem_id: E571
- collection: erdos
- question_id: erdos:571
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/571.lean#erdos_571
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Show that for any rational $\alpha \in [1,2)$ there exists a bipartite graph $G$ such that $$\mathrm{ex}(n;G)\asymp n^{\alpha}.$$ The proof constructs balanced rooted models for all rational parameters. Its upper-bound closure replaces old edges by paths of arbitrary length, adds two color-class hubs, and commutes with positive rooted powers.
- notes: Erdos Problem 571 -- https://www.erdosproblems.com/571
- track: solved
- answer_shape: proof
- source_stem: 571
- mathdb_ref: erdos:571
- source_namespace: Erdos571
- source_theorem: erdos_571
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter SimpleGraph

namespace Problem

abbrev Target : Prop :=
    ∀ α : ℚ, 1 ≤ α → α < 2 →
      ∃ q : ℕ, ∃ G : SimpleGraph (Fin q), G.IsBipartite ∧
        Asymptotics.IsTheta atTop
          (fun n : ℕ => (extremalNumber n G : ℝ))
          (fun n : ℕ => (n : ℝ) ^ (α : ℝ))

end Problem
