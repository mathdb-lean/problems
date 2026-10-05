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

- problem_id: K1_74
- collection: kourovka
- question_id: kourovka:1_74
- source: formal-conjectures
- source_locator: FormalConjectures/Kourovka/1_74.lean#kourovka_1_74
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Describe all minimal topological groups, that is, all non-discrete Hausdorff topological groups whose proper closed subgroups are all discrete.
- notes: Kourovka Notebook 1_74
- track: open
- answer_shape: value
- answer_type: ∀ (G : Type) [Group G] [TopologicalSpace G], Prop
- answer_pinned: false
- answer_pinned_reason: unclassified
- source_stem: 1_74
- source_namespace: Kourovka.«1.74»
- source_theorem: kourovka_1_74
- source_category: research open
- source_ams: 20 22
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
A minimal topological group in Platonov's sense: a non-discrete Hausdorff
topological group all of whose proper closed subgroups are discrete.
-/
def IsMinimalTopologicalGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  IsTopologicalGroup G ∧ T2Space G ∧ ¬ DiscreteTopology G ∧
    ∀ H : Subgroup G, H ≠ ⊤ → IsClosed (H : Set G) → DiscreteTopology H

/--
A Tarski monster group: an infinite group in which every non-trivial proper
subgroup has order a fixed prime $p$.
-/
def IsTarskiMonster (G : Type*) [Group G] : Prop :=
  Infinite G ∧ ∃ p : ℕ, p.Prime ∧
    ∀ H : Subgroup G, H ≠ ⊥ → H ≠ ⊤ → Nat.card H = p

abbrev Target (value : ∀ (G : Type) [Group G] [TopologicalSpace G], Prop) : Prop :=
    ∀ (G : Type) [Group G] [TopologicalSpace G],
      IsMinimalTopologicalGroup G ↔
        value G

end Problem
