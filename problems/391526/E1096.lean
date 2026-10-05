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

- problem_id: E1096
- collection: erdos
- question_id: erdos:1096
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1096.lean#erdos_1096
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $1<q<1+\epsilon$ and consider the set of numbers of the shape $\sum_{i\in S}q^i$ (for all finite $S$), ordered by size as $0=x_1<x_2<\cdots$. Is it true that, provided $\epsilon>0$ is sufficiently small, $x_{k+1}-x_k \to 0$? This was solved affirmatively by Erdős and Komornik [ErKo98], who proved the conclusion whenever $1<q<\sqrt{q_1}$, where $q_1$ is the second Pisot-Vijayaraghavan number.
- notes: Erdos Problem 1096 -- https://www.erdosproblems.com/1096
- track: solved
- answer_shape: decide
- source_stem: 1096
- mathdb_ref: erdos:1096
- source_namespace: Erdos1096
- source_theorem: erdos_1096
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter
open scoped Topology

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ ε > 0, ∀ q, 1 < q → q < 1 + ε →
    ∀ x : ℕ → ℝ, StrictMono x → Set.range x = { ∑ i ∈ S, q ^ i | S : Finset ℕ } →
    Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0)

end Problem
