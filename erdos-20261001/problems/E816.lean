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

- problem_id: E816
- collection: erdos
- question_id: erdos:816
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/816.lean#erdos_816
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be a graph with $2n+1$ vertices and $n^2+n+1$ edges. Must $G$ contain two vertices of the same degree which are joined by a path of length $3$? A problem of Erdős and Hajnal. The example of $K_{n,n+1}$ shows that this fails if we only have $n^2+n$ edges. This is true, and was proved by Chen and Ma [ChMa25], who prove the stronger statement that, provided $n\geq 600$, all graphs with $2n+1$ vertices and at least $n^2+n$ edges contain two vertices of the same degree joined by a path of length $3$, except $K_{n,n+1}$. For $n = 1$ the graph is a triangle, which contains no path of length $3$, so we assume $n \geq 2$.
- notes: Erdos Problem 816 -- https://www.erdosproblems.com/816
- track: solved
- answer_shape: decide
- source_stem: 816
- mathdb_ref: erdos:816
- source_namespace: Erdos816
- source_theorem: erdos_816
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open SimpleGraph

namespace Problem

open scoped Classical in
/--
`G` contains two vertices of the same degree which are joined by a path of length `3`.
-/
def HasEqualDegreePathThree {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ u v : V, u ≠ v ∧ G.degree u = G.degree v ∧ ∃ p : G.Walk u v, p.IsPath ∧ p.length = 3

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ n : ℕ, 2 ≤ n → ∀ G : SimpleGraph (Fin (2 * n + 1)),
        G.edgeFinset.card = n ^ 2 + n + 1 → HasEqualDegreePathThree G

end Problem
