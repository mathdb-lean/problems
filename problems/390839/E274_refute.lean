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

- problem_id: E274_refute
- collection: erdos
- question_id: erdos:274
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/274.lean#erdos_274
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $G$ is a group, can there exist an exact covering of $G$ by more than one coset of different sizes? (i.e. each element is contained in exactly one of the cosets.) The conjectured answer is no: in every such exact covering, two of the subgroups have the same cardinality.
- notes: Erdos Problem 274 -- https://www.erdosproblems.com/274
- track: open
- answer_shape: refute
- pair_id: E274
- pair_role: refute
- source_stem: 274
- mathdb_ref: erdos:274
- source_namespace: Erdos274
- source_theorem: erdos_274
- source_category: research open
- source_ams: 20
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Pointwise Cardinal

namespace Problem

-- TODO(callesonne): add already proved results from the wiki page

/-- An exact covering of a group `G` is a finite collection of subgroups `{H_1, ..., H_k}` and
representative `{g_1, ..., g_k}` such that the cosets `g_iH_i` are pairwise disjoint and their
union covers `G`.

Note that this differs from `Partition (α := Subgroup G)` because the covering condition there
invokes `Subgroup.sup` which is subgroup generation and thus stronger than union. This definition
is easier to use in this context than the alternative `Partition (α := Set G)`, which lacks
subgroup definitions such as `Subgroup.index`. -/
structure Group.ExactCovering (G : Type*) [Group G] (ι : Type*) [Fintype ι] where
  parts : ι → Subgroup G
  reps : ι → G
  nonempty (i : ι) : (parts i : Set G).Nonempty
  disjoint : (Set.univ (α := ι)).PairwiseDisjoint fun (i : ι) ↦ reps i • (parts i : Set G)
  covers : ⋃ i, reps i • (parts i : Set G) = Set.univ

abbrev Target : Prop :=
    ¬ (
      ∃ (G : Type*) (_ : Group G),
          1 < ENat.card G ∧ ∃ (ι : Type*) (_ : Fintype ι) (P : Group.ExactCovering G ι),
          1 < Fintype.card ι ∧ ∀ i j, i ≠ j → #(P.parts i) ≠ #(P.parts j)
    )

end Problem
