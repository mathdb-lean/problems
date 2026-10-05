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

- problem_id: RChvatal_exists_maximal_star
- collection: paper
- question_id: paper:Chvatal
- source: formal-conjectures
- source_locator: FormalConjectures/Paper/Chvatal.lean#exists_maximal_star
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If F is a decreasing family of sets of some finite type α, then there is some element x of α such that the family consisting of all members of F containing x is an intersecting subfamily of F with maximal cardinality.
- notes: Problem from Chvatal -- https://users.encs.concordia.ca/~chvatal/conjecture.html
- track: open
- answer_shape: proof
- source_stem: Chvatal
- source_namespace: Chvatal
- source_theorem: exists_maximal_star
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

/-- A family F of sets is Decreasing if it is closed under taking subsets. -/
def Decreasing (F : Finset (Finset α)) : Prop :=
    ∀ A B : Finset α, B ⊆ A → A ∈ F → B ∈ F

/-- A family F of sets is Intersecting if each pair of members has nonempty intersection. -/
def Intersecting (F : Finset (Finset α)) : Prop :=
    ∀ A ∈ F, ∀ B ∈ F, A ∩ B ≠ ∅

abbrev Target : Prop :=
    ∀ F : Finset (Finset α), Decreasing F →
        ∃ x : α, ∀ G, G ⊆ F → Intersecting G → G.card ≤ { A ∈ F | x ∈ A }.card

end Problem
