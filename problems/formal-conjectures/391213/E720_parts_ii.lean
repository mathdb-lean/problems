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

- problem_id: E720_parts_ii
- collection: erdos
- question_id: erdos:720
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/720.lean#erdos_720.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that, if $P_n$ is the path of length $n$, then $\hat{R}(P_n)/n^2 \to 0$? The answer is yes: Beck [Be83b] proved that in fact $\hat{R}(P_n)\ll n$.
- notes: Erdos Problem 720 -- https://www.erdosproblems.com/720
- track: solved
- answer_shape: decide
- source_stem: 720
- mathdb_ref: erdos:720
- source_namespace: Erdos720
- source_theorem: erdos_720.parts.ii
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter SimpleGraph

namespace Problem

/-- The size Ramsey number $\hat{R}(G)$ of `G`: the least number of edges of a graph which is
Ramsey for `G`. -/
noncomputable abbrev sizeRamseyNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sizeRamsey G G

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        Tendsto (fun n : ℕ ↦ (sizeRamseyNumber (pathGraph (n + 1)) : ℝ) / (n : ℝ) ^ 2) atTop
          (nhds 0)

end Problem
