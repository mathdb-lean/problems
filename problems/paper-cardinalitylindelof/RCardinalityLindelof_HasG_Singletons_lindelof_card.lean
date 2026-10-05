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

- problem_id: RCardinalityLindelof_HasG_Singletons_lindelof_card
- collection: paper
- question_id: paper:CardinalityLindelof
- source: formal-conjectures
- source_locator: FormalConjectures/Paper/CardinalityLindelof.lean#HasGδSingletons.lindelof_card
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a Lindelöf Tychonoff space with singletons as Gδ sets with cardinality greater than the continuum? Note: the cited paper uses a blanket convention that all spaces are Tychonoff.
- notes: Problem from CardinalityLindelof -- https://www.math.md/files/basm/y2013-n2-3/y2013-n2-3-(pp37-46).pdf.pdf
- track: open
- answer_shape: proof
- source_stem: CardinalityLindelof
- source_namespace: CardinalityLindelof
- source_theorem: HasGδSingletons.lindelof_card
- source_category: research open
- source_ams: 54
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Cardinal

namespace Problem

abbrev Target : Prop :=
    ∃ (X : Type) (_ : TopologicalSpace X),
      T35Space X ∧ HasGδSingletons X ∧ LindelofSpace X ∧ 𝔠 < #X

end Problem
