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

- problem_id: E559
- collection: erdos
- question_id: erdos:559
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/559.lean#erdos_559
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\hat{R}(G)$ denote the size Ramsey number, the minimal number of edges $m$ such that there is a graph $H$ with $m$ edges that is Ramsey for $G$. If $G$ has $n$ vertices and maximum degree $d$ then prove that $$\hat{R}(G)\ll_d n.$$ This was disproved for $d=3$ by Rödl and Szemerédi [RoSz00], who constructed a graph on $n$ vertices with maximum degree $3$ such that $\hat{R}(G)\gg n(\log n)^{c}$ for some absolute constant $c>0$.
- notes: Erdos Problem 559 -- https://www.erdosproblems.com/559
- track: solved
- answer_shape: decide
- source_stem: 559
- mathdb_ref: erdos:559
- source_namespace: Erdos559
- source_theorem: erdos_559
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Real SimpleGraph

namespace Problem

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ d : ℕ, ∃ C : ℝ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
          G.maxDegree ≤ d → (sizeRamsey G G : ℝ) ≤ C * Fintype.card V

end Problem
