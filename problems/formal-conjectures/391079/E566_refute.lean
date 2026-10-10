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

- problem_id: E566_refute
- collection: erdos
- question_id: erdos:566
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/566.lean#erdos_566
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be such that any subgraph on $k$ vertices has at most $2k-3$ edges. Is it true that, if $H$ has $m$ edges and no isolated vertices, then $R(G,H) \ll m$? In other words: if $G$ is sparse (every induced subgraph on $k$ vertices has $≤ 2k-3$ edges), is $G$ Ramsey size linear?
- notes: Erdos Problem 566 -- https://www.erdosproblems.com/566
- track: open
- answer_shape: refute
- pair_id: E566
- pair_role: refute
- source_stem: 566
- mathdb_ref: erdos:566
- source_namespace: Erdos566
- source_theorem: erdos_566
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

abbrev Target : Prop :=
    ¬ (
      ∀ (p : ℕ) (G : SimpleGraph (Fin p)),
            (∀ S : Finset (Fin p), 2 ≤ S.card → (G.induce S).edgeSet.ncard ≤ 2 * S.card - 3) →
            G.IsRamseySizeLinear
    )

end Problem
