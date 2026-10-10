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

- problem_id: E567_parts_ii_prove
- collection: erdos
- question_id: erdos:567
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/567.lean#erdos_567.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Erdős Problem 567 (K33)** Is $K_{3,3}$ Ramsey size linear?
- notes: Erdos Problem 567 -- https://www.erdosproblems.com/567
- track: open
- answer_shape: prove
- pair_id: E567_parts_ii
- pair_role: prove
- source_stem: 567
- mathdb_ref: erdos:567
- source_namespace: Erdos567
- source_theorem: erdos_567.parts.ii
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph
open scoped Finset

/-- $Q_3$ is the 3-dimensional hypercube graph (8 vertices, 12 edges).
Vertices are 3-bit vectors. Two vertices are adjacent iff they differ in exactly one bit. -/
abbrev Q3 : SimpleGraph (Fin 3 → Bool) := hypercube 3

/-- $K_{3,3}$ is the complete bipartite graph with partition sizes 3, 3 (6 vertices, 9 edges). -/
def K33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)

/-- $H_5$ is $C_5$ with two vertex-disjoint chords (5 vertices, 7 edges).
Also known as $K_4^*$ (the graph obtained from $K_4$ by subdividing one edge). -/
def H5 : SimpleGraph (Fin 5) :=
  .cycleGraph 5 ⊔ .edge 0 2 ⊔ .edge 1 3

abbrev Target : Prop :=
    IsRamseySizeLinear K33

end Problem
