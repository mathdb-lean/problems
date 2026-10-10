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

- problem_id: E760
- collection: erdos
- question_id: erdos:760
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/760.lean#erdos_760
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The cochromatic number of $G$, denoted by $\zeta(G)$, is the minimum number of colours needed to colour the vertices of $G$ such that each colour class induces either a complete graph or independent set. If $G$ is a graph with chromatic number $\chi(G)=m$ then must $G$ contain a subgraph $H$ with $$ \zeta(H) \gg \frac{m}{\log m}? $$ A problem of Erdős and Gimbel, who proved that there must exist a subgraph $H$ with $$ \zeta(H) \gg \left(\frac{m}{\log m}\right)^{1/2}. $$ The proposed bound would be best possible, as shown by taking $G$ to be a complete graph. The answer is yes, proved by Alon, Krivelevich, and Sudakov.
- notes: Erdos Problem 760 -- https://www.erdosproblems.com/760
- track: solved
- answer_shape: decide
- source_stem: 760
- mathdb_ref: erdos:760
- source_namespace: Erdos760
- source_theorem: erdos_760
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ c > (0 : ℝ), ∀ (V : Type*) [Finite V] (G : SimpleGraph V) (m : ℕ),
          G.chromaticNumber = (m : ℕ∞) →
            ∃ H : G.Subgraph, ∃ k : ℕ, ((k : ℕ∞) ≤ H.coe.cochromaticNumber) ∧
              (c * (m : ℝ) / Real.log (m : ℝ) ≤ (k : ℝ))

end Problem
