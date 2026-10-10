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

- problem_id: E87_parts_i_refute
- collection: erdos
- question_id: erdos:87
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/87.lean#erdos_87.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $0 < \epsilon < 1$. Is it true that, if $k$ is sufficiently large, then $$R(G) > (1-\epsilon)^k R(k)$$ for every graph $G$ with chromatic number $\chi(G)=k$? The restriction $\epsilon < 1$ excludes negative bases in $(1-\epsilon)^k$. This problem is #12 in Ramsey Theory in the graphs problem collection.
- notes: Erdos Problem 87 -- https://www.erdosproblems.com/87
- track: open
- answer_shape: refute
- pair_id: E87_parts_i
- pair_role: refute
- source_stem: 87
- mathdb_ref: erdos:87
- source_namespace: Erdos87
- source_theorem: erdos_87.parts.i
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∀ ε > (0 : ℝ), ε < 1 → ∀ᶠ k : ℕ in atTop,
            ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.chromaticNumber = (k : ℕ∞) →
              (SimpleGraph.diagonalGraphRamsey G : ℝ) >
                (1 - ε) ^ k * (SimpleGraph.diagonalRamsey k : ℝ)
    )

end Problem
