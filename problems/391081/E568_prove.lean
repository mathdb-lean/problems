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

- problem_id: E568_prove
- collection: erdos
- question_id: erdos:568
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/568.lean#erdos_568
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be a graph such that $R(G,T_n)\ll n$ for any tree $T_n$ on $n$ vertices and $R(G,K_n)\ll n^2$. Is it true that, for any $H$ with $m$ edges and no isolated vertices, $$R(G,H)\ll m?$$ In other words, is $G$ Ramsey size linear? This problem is #33 in Ramsey Theory in the graphs problem collection.
- notes: Erdos Problem 568 -- https://www.erdosproblems.com/568
- track: open
- answer_shape: prove
- pair_id: E568
- pair_role: prove
- source_stem: 568
- mathdb_ref: erdos:568
- source_namespace: Erdos568
- source_theorem: erdos_568
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
          (∃ c₁ > (0 : ℝ), ∀ (n : ℕ) (T : SimpleGraph (Fin n)),
            T.IsTree → (SimpleGraph.graphRamsey G T : ℝ) ≤ c₁ * n) →
          (∃ c₂ > (0 : ℝ), ∀ (n : ℕ),
            (SimpleGraph.graphRamsey G (SimpleGraph.completeGraph (Fin n)) : ℝ) ≤ c₂ * (n : ℝ) ^ 2) →
          G.IsRamseySizeLinear

end Problem
