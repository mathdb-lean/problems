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

- problem_id: E599
- collection: erdos
- question_id: erdos:599
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/599.lean#erdos_599
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Erdős Problem 599** (the Erdős–Menger conjecture). Let $G$ be a (possibly infinite) graph and let $A, B$ be disjoint independent sets of vertices. Must there exist a family $P$ of pairwise vertex-disjoint paths from $A$ to $B$, and a set $S$ of vertices containing exactly one vertex from each path in $P$, such that every path from $A$ to $B$ contains at least one vertex of $S$? For finite $G$ this is equivalent to Menger's theorem. The answer is **yes**, proved by Aharoni and Berger [AhBe09].
- notes: Erdos Problem 599 -- https://www.erdosproblems.com/599
- track: solved
- answer_shape: decide
- source_stem: 599
- mathdb_ref: erdos:599
- source_namespace: Erdos599
- source_theorem: erdos_599
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open SimpleGraph

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (V : Type) (G : SimpleGraph V) (A B : Set V),
          Disjoint A B → G.IsIndepSet A → G.IsIndepSet B →
          ∃ (ι : Type) (a b : ι → V) (p : ∀ i, G.Walk (a i) (b i)) (S : Set V),
            (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (p i).IsPath) ∧
            (Pairwise fun i j => Disjoint {v | v ∈ (p i).support} {v | v ∈ (p j).support}) ∧
            S ⊆ {v | ∃ i, v ∈ (p i).support} ∧
            (∀ i, ∃! v, v ∈ S ∧ v ∈ (p i).support) ∧
            (∀ a' ∈ A, ∀ b' ∈ B, ∀ q : G.Walk a' b', q.IsPath → ∃ v ∈ q.support, v ∈ S)

end Problem
