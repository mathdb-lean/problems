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

- problem_id: E1007
- collection: erdos
- question_id: erdos:1007
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1007.lean#erdos_1007
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The dimension of a graph $G$ is the minimal $n$ such that $G$ can be embedded in $\mathbb{R}^n$ such that every edge of $G$ is a unit line segment. What is the smallest number of edges in a graph with dimension $4$? Answer: The smallest number of edges is $9$, achieved solely by $K_{3,3}$, proved by House [Ho13]. An alternative proof was given by Chaffee and Noble [ChNo16], who also prove that the smallest number of edges in a graph of dimension $5$ is $15$ (achieved by $K_6$ and $K_{1,3,3}$).
- notes: Erdos Problem 1007 -- https://www.erdosproblems.com/1007
- track: solved
- answer_shape: proof
- source_stem: 1007
- mathdb_ref: erdos:1007
- source_namespace: Erdos1007
- source_theorem: erdos_1007
- source_category: research solved
- source_ams: 5 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open scoped EuclideanGeometry

variable {V : Type*}

/-- The complete tripartite graph $K_{1,3,3}$. -/
abbrev K133 := SimpleGraph.completeMultipartiteGraph fun i : Fin 3 => Fin (![1, 3, 3] i)

abbrev Target : Prop :=
    IsLeast {m | ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.HasDimension 4 ∧ G.edgeSet.ncard = m}
      9

end Problem
