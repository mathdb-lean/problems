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

- problem_id: E842
- collection: erdos
- question_id: erdos:842
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/842.lean#erdos_842
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be a graph on $3n$ vertices formed by taking $n$ vertex disjoint triangles and adding a Hamiltonian cycle (with all new edges) between these vertices. Does $G$ have chromatic number at most $3$? The answer is yes, proved by Fleischner and Stiebitz [FlSt92].
- notes: Erdos Problem 842 -- https://www.erdosproblems.com/842
- track: solved
- answer_shape: decide
- source_stem: 842
- mathdb_ref: erdos:842
- source_namespace: Erdos842
- source_theorem: erdos_842
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open SimpleGraph

namespace Problem

/-- `G` is a graph on `3n` vertices formed by taking `n` vertex-disjoint triangles `T` and adding
a Hamiltonian cycle `C` (with all new edges): `G = T ⊔ C` with `T` and `C` edge-disjoint. -/
def IsTrianglesPlusHamiltonianCycle {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ T C : SimpleGraph V, G = T ⊔ C ∧ Disjoint T C ∧
    (∃ e : V ≃ Fin n × Fin 3, ∀ u v, T.Adj u v ↔ u ≠ v ∧ (e u).1 = (e v).1) ∧
    ∃ e : Fin (3 * n) ≃ V, C = (cycleGraph (3 * n)).map e.toEmbedding

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (V : Type) (G : SimpleGraph V) (n : ℕ), IsTrianglesPlusHamiltonianCycle G n →
          G.chromaticNumber ≤ 3

end Problem
