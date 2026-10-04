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

- problem_id: E134
- collection: erdos
- question_id: erdos:134
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/134.lean#erdos_134
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\epsilon,\delta>0$ and $n$ be sufficiently large in terms of $\epsilon$ and $\delta$. Let $G$ be a triangle-free graph on $n$ vertices with maximum degree $<n^{1/2-\epsilon}$. Can $G$ be made into a triangle-free graph with diameter $2$ by adding at most $\delta n^2$ edges? Asked by Erdős and Gyárfás, who proved that this is the case when $G$ has maximum degree $\ll \log n/\log\log n$. A construction of Simonovits shows that this conjecture is false if we just have maximum degree $\leq Cn^{1/2}$, for some large enough $C$. In this note Alon solves this problem in a strong form, in particular proving that a triangle-free graph on $n$ vertices with maximum degree $<n^{1/2-\epsilon}$ can be made into a triangle-free graph with diameter $2$ by adding at most $O(n^{2-\epsilon})$ edges.
- notes: Erdos Problem 134 -- https://www.erdosproblems.com/134
- track: solved
- answer_shape: decide
- source_stem: 134
- mathdb_ref: erdos:134
- source_namespace: Erdos134
- source_theorem: erdos_134
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
        ∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ),
        ∃ N : ℕ, ∀ n ≥ N, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          G.CliqueFree 3 →
          (∀ v : Fin n, (G.degree v : ℝ) < Real.rpow (n : ℝ) ((1 : ℝ) / 2 - ε)) →
          ∃ (H : SimpleGraph (Fin n)) (_ : DecidableRel H.Adj),
            G ≤ H ∧
            H.CliqueFree 3 ∧
            (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
            ((H.edgeFinset \ G.edgeFinset).card : ℝ) ≤ δ * (n : ℝ) ^ 2

end Problem
