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

- problem_id: E751_parts_i
- collection: erdos
- question_id: erdos:751
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/751.lean#erdos_751.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be a graph with chromatic number $\chi(G)=4$. If $m_1<m_2<\cdots$ are the lengths of the cycles in $G$ then can $\min(m_{i+1}-m_i)$ be arbitrarily large? The answer is no: Bondy and Vince [BoVi98] proved that every graph with minimum degree at least $3$ has two cycles whose lengths differ by at most $2$, and hence the same is true for every graph with chromatic number $4$. `erdos_751.variants.finite` below carries the Lean proof. It assumes a finite vertex type, where this quantifies over any `V : Type`, and the two are joined by de Bruijn-Erdős: a graph that is not $3$-colourable has a finite subgraph that is not $3$-colourable, and cycles of that subgraph are cycles of the whole. Mathlib does not have de Bruijn-Erdős, so that step is not formalised here.
- notes: Erdos Problem 751 -- https://www.erdosproblems.com/751
- track: solved
- answer_shape: decide
- source_stem: 751
- mathdb_ref: erdos:751
- source_namespace: Erdos751
- source_theorem: erdos_751.parts.i
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      ∀ k : ℕ, ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = 4 ∧
        ∀ m ∈ G.cycleLengths, ∀ m' ∈ G.cycleLengths, m < m' → m + k ≤ m'

end Problem
