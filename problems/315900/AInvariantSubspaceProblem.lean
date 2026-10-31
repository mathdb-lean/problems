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

import FormalConjecturesUtil

/-!
Stated in this library. The definition and the statement follow
`FormalConjectures/Wikipedia/InvariantSubspaceProblem.lean` in formal-conjectures
(e04cc601), where the Hilbert space is a section `variable`. The converter refuses
a statement whose `Target` would silently take a parameter its written signature
does not show (`unsupported_section_variable`), so the problem is restated here
with the space bound explicitly, in `Type`. Nothing else changes.

- problem_id: AInvariantSubspaceProblem
- collection: authored
- question_id: authored:InvariantSubspaceProblem
- source: mathdb-lean
- source_locator: authored/InvariantSubspaceProblem.lean#Target
- prose: Every bounded linear operator on a complex separable Hilbert space of dimension at least 2 has a non-trivial closed invariant subspace: a closed linear subspace different from the whole space and from zero that the operator maps into itself.
- notes: Invariant subspace problem -- https://en.wikipedia.org/wiki/Invariant_subspace_problem
- track: open
- answer_shape: proof
- source_category: research open
- source_ams: 47
- generator: adapters/authored/adapter.py
-/

namespace Problem

/-- `ClosedInvariantSubspace T` is the type of non-trivial (different from `H` and `{0}`) closed
subspaces of a complex vector space `H` that are invariant under the action of the linear map
`T`. -/
structure ClosedInvariantSubspace {H : Type} [NormedAddCommGroup H] [Module ℂ H]
    (T : H →L[ℂ] H) where
  toSubspace : Submodule ℂ H
  ne_bot : toSubspace ≠ ⊥
  ne_top : toSubspace ≠ ⊤
  is_closed : IsClosed (toSubspace : Set H)
  is_fixed : toSubspace.map T.toLinearMap ≤ toSubspace

/-- Every bounded linear operator `T : H → H` on a separable complex Hilbert space `H` of
dimension at least 2 has a non-trivial closed `T`-invariant subspace. Dimension at least 2 is
needed because otherwise every subspace is `H` or `{0}`. -/
abbrev Target : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [TopologicalSpace.SeparableSpace H] [CompleteSpace H],
    2 ≤ Module.rank ℂ H → ∀ T : H →L[ℂ] H, Nonempty (ClosedInvariantSubspace T)

end Problem

/-!
- source_version: 2fe7c76111373ea1d5503c074350e836cf33de46
-/
