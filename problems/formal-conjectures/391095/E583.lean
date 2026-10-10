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

- problem_id: E583
- collection: erdos
- question_id: erdos:583
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/583.lean#erdos_583
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Every connected graph on $n$ vertices can be partitioned into at most $\lceil n/2\rceil$ edge-disjoint paths. A problem of Erdős and Gallai.
- notes: Erdos Problem 583 -- https://www.erdosproblems.com/583
- track: open
- answer_shape: proof
- source_stem: 583
- mathdb_ref: erdos:583
- source_namespace: Erdos583
- source_theorem: erdos_583
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open SimpleGraph

namespace Problem

/--
A subgraph `H` of `G` is a path subgraph if it is the subgraph traced out by a path in `G`,
i.e. a walk with no repeated vertices.
-/
def IsPathSubgraph {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) : Prop :=
  ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ H = p.toSubgraph

abbrev Target : Prop :=
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsPathSubgraph H) ∧
        IsDecomposition G D ∧
        D.card ≤ ⌈(Fintype.card V : ℚ) / 2⌉₊

end Problem
