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

- problem_id: E701_prove
- collection: erdos
- question_id: erdos:701
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/701.lean#erdos_701
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\mathcal{F}$ be a family of sets closed under taking subsets (i.e. if $B\subseteq A\in\mathcal{F}$ then $B\in \mathcal{F}$). There exists some element $x$ such that whenever $\mathcal{F}'\subseteq \mathcal{F}$ is an intersecting subfamily we have $$\lvert \mathcal{F}'\rvert \leq \lvert \{ A\in \mathcal{F} : x\in A\}\rvert.$$
- notes: Erdos Problem 701 -- https://www.erdosproblems.com/701
- track: open
- answer_shape: prove
- pair_id: E701
- pair_role: prove
- source_stem: 701
- mathdb_ref: erdos:701
- source_namespace: Erdos701
- source_theorem: erdos_701
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Cardinal

abbrev Target : Prop :=
    ∀ {X : Type} [Nonempty X] [Fintype X],
        ∀ (F : Set (Set X)), IsLowerSet F →
          ∃ x : X, ∀ᵉ (F' ⊆ F),
            F'.Intersecting →
              (#F' ≤ #{ A : Set X | A ∈ F ∧ x ∈ A })

end Problem
