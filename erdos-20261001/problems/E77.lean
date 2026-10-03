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

- problem_id: E77
- collection: erdos
- question_id: erdos:77
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/77.lean#erdos_77
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $R(k)$ is the Ramsey number for $K_k$, the minimal $n$ such that every $2$-colouring of the edges of $K_n$ contains a monochromatic copy of $K_k$, then find the value of $$\lim_{k\to \infty}R(k)^{1/k}.$$ This problem is #3 in Ramsey Theory in the graphs problem collection.
- notes: Erdos Problem 77 -- https://www.erdosproblems.com/77
- track: open
- answer_shape: value
- answer_type: ℝ
- answer_pinned: true
- answer_pinned_reason: limit_is_unique
- source_stem: 77
- mathdb_ref: erdos:77
- source_namespace: Erdos77
- source_theorem: erdos_77
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Topology

namespace Problem

abbrev Target (value : ℝ) : Prop :=
    Filter.Tendsto (fun k : ℕ ↦ (SimpleGraph.diagonalRamsey k : ℝ) ^ (1 / (k : ℝ)))
      Filter.atTop (𝓝 value)

end Problem
