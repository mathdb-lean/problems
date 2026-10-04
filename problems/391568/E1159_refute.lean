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

- problem_id: E1159_refute
- collection: erdos
- question_id: erdos:1159
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1159.lean#erdos_1159
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Determine whether there exists a constant $C>1$ such that the following holds. Let $P$ be a finite [projective plane](https://en.wikipedia.org/wiki/Projective_plane). Must there exist a set of points $S$ such that $1\leq \lvert S\cap \ell\rvert \leq C$ for all lines $\ell$?
- notes: Erdos Problem 1159 -- https://www.erdosproblems.com/1159
- track: open
- answer_shape: refute
- pair_id: E1159
- pair_role: refute
- source_stem: 1159
- mathdb_ref: erdos:1159
- source_namespace: Erdos1159
- source_theorem: erdos_1159
- source_category: research open
- source_ams: 5 51
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Configuration

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∃ C : ℕ, 1 < C ∧
            ∀ (P L : Type) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L),
              ∀ _ : ProjectivePlane P L, ∃ S : Set P, ∀ l : L,
                1 ≤ (S ∩ {p : P | p ∈ l}).ncard ∧ (S ∩ {p : P | p ∈ l}).ncard ≤ C
    )

end Problem
