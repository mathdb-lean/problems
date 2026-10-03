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

- problem_id: E22
- collection: erdos
- question_id: erdos:22
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/22.lean#erdos_22
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\epsilon > 0$ and let $n$ be sufficiently large depending on $\epsilon$. Is there a graph on $n$ vertices with at least $n^2/8$ many edges which contains no $K_4$, such that the largest independent set has size at most $\epsilon n$? This is true, as proved by Fox, Loh, and Zhao [FLZ15].
- notes: Erdos Problem 22 -- https://www.erdosproblems.com/22
- track: solved
- answer_shape: decide
- source_stem: 22
- mathdb_ref: erdos:22
- source_namespace: Erdos22
- source_theorem: erdos_22
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter SimpleGraph

namespace Problem

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop,
          ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
            (G.indepNum : ℝ) ≤ ε * n ∧ (n : ℝ) ^ 2 / 8 ≤ G.edgeFinset.card

end Problem
