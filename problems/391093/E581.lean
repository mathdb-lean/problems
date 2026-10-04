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

- problem_id: E581
- collection: erdos
- question_id: erdos:581
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/581.lean#erdos_581
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(m)$ be the maximal $k$ such that a triangle-free graph on $m$ edges must contain a bipartite graph with $k$ edges. Determine $f(m)$. Resolved by Alon [Al96], who showed that there exist constants $c_1,c_2>0$ such that $$\frac{m}{2}+c_1m^{4/5}\leq f(m)\leq \frac{m}{2}+c_2m^{4/5}.$$
- notes: Erdos Problem 581 -- https://www.erdosproblems.com/581
- track: solved
- answer_shape: proof
- source_stem: 581
- mathdb_ref: erdos:581
- source_namespace: Erdos581
- source_theorem: erdos_581
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open SimpleGraph

namespace Problem

/-- `f m` is the maximal `k` such that every triangle-free graph on `m` edges contains a
bipartite subgraph with `k` edges. -/
noncomputable def f (m : ℕ) : ℕ :=
  sSup {k | ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    G.edgeSet.ncard = m → ∃ H ≤ G, H.IsBipartite ∧ k ≤ H.edgeSet.ncard}

abbrev Target : Prop :=
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ m : ℕ,
        (m : ℝ) / 2 + c₁ * (m : ℝ) ^ (4 / 5 : ℝ) ≤ f m ∧
          (f m : ℝ) ≤ (m : ℝ) / 2 + c₂ * (m : ℝ) ^ (4 / 5 : ℝ)

end Problem
