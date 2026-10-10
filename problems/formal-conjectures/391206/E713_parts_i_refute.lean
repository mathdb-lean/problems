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

- problem_id: E713_parts_i_refute
- collection: erdos
- question_id: erdos:713
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/713.lean#erdos_713.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that, for every bipartite graph $G$, there exists some $\alpha\in [1,2)$ and $c>0$ such that $$\mathrm{ex}(n;G)\sim cn^\alpha?$$ The condition that $G$ have at least two edges excludes degenerate forbidden graphs whose extremal number is eventually zero, for which the displayed asymptotic with $c>0$ is impossible.
- notes: Erdos Problem 713 -- https://www.erdosproblems.com/713
- track: open
- answer_shape: refute
- pair_id: E713_parts_i
- pair_role: refute
- source_stem: 713
- mathdb_ref: erdos:713
- source_namespace: Erdos713
- source_theorem: erdos_713.parts.i
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter SimpleGraph

namespace Problem

open scoped Classical in
abbrev Target : Prop :=
    ¬ (
      ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ G.edgeFinset.card →
            ∃ α c : ℝ, α ∈ Set.Ico 1 2 ∧ 0 < c ∧
              Asymptotics.IsEquivalent atTop
                (fun n : ℕ => (extremalNumber n G : ℝ))
                (fun n : ℕ => c * (n : ℝ) ^ α)
    )

end Problem
