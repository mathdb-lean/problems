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

- problem_id: E71
- collection: erdos
- question_id: erdos:71
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/71.lean#erdos_71
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that for every infinite arithmetic progression $P$ which contains even numbers there is some constant $c=c(P)$ such that every graph with average degree at least $c$ contains a cycle whose length is in $P$? In [Er82e] Erdős credits this conjecture to himself and Burr. This has been proved by Bollobás [Bo77]. The best dependence of the constant $c(P)$ is unknown. The infinite arithmetic progression is encoded as a set $P \subseteq \mathbb{N}$ satisfying `P.IsAPOfLength ⊤` (which forces a positive common difference), and "contains even numbers" as the existence of an even element. The average degree of a finite simple graph is `SimpleGraph.averageDegree`, i.e. $(\sum_v \deg v)/|V| \in \mathbb{Q}$, and a cycle whose length is in $P$ is a cycle walk `w` with `w.length ∈ P`.
- notes: Erdos Problem 71 -- https://www.erdosproblems.com/71
- track: solved
- answer_shape: decide
- source_stem: 71
- mathdb_ref: erdos:71
- source_namespace: Erdos71
- source_theorem: erdos_71
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
        ∀ P : Set ℕ, P.IsAPOfLength ⊤ → (∃ n ∈ P, Even n) →
          ∃ c : ℚ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
            [DecidableRel G.Adj], c ≤ G.averageDegree →
              ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length ∈ P

end Problem
