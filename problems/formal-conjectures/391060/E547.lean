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

- problem_id: E547
- collection: erdos
- question_id: erdos:547
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/547.lean#erdos_547
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $T$ is a tree on $n$ vertices then $$R(T) \leq 2n-2.$$ This problem is #14 in Ramsey Theory in the graphs problem collection.
- notes: Erdos Problem 547 -- https://www.erdosproblems.com/547
- track: open
- answer_shape: proof
- source_stem: 547
- mathdb_ref: erdos:547
- source_namespace: Erdos547
- source_theorem: erdos_547
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 2 ≤ n) (T : SimpleGraph (Fin n)),
      T.IsTree → SimpleGraph.diagonalGraphRamsey T ≤ 2 * n - 2

end Problem
