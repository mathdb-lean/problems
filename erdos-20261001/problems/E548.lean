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

- problem_id: E548
- collection: erdos
- question_id: erdos:548
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/548.lean#erdos_548
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $n\geq k+1$. Every graph on $n$ vertices with at least $\frac{k-1}{2}n+1$ edges contains every tree on $k+1$ vertices.
- notes: Erdos Problem 548 -- https://www.erdosproblems.com/548
- track: solved
- answer_shape: proof
- source_stem: 548
- mathdb_ref: erdos:548
- source_namespace: Erdos548
- source_theorem: erdos_548
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open SimpleGraph

namespace Problem

abbrev Target : Prop :=
    ∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n))
        (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ))
        (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree),
      T.IsContained G

end Problem
