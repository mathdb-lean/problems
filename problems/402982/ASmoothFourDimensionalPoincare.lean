/-
Copyright 2026 The Formal Conjectures Authors.
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
Stated in this library. The definition follows `SmoothConjectureFor` in
formal-conjectures `FormalConjectures/Millennium/Poincare.lean` (e04cc601),
where the four-dimensional case is `poincare_conjecture.variants.smooth_dimension_four`,
a variant beside the solved three-dimensional target. It is a problem of its
own, so it is stated on its own here. Two deliberate differences from upstream:
the manifold is required to be compact, as in the usual statement about closed
homotopy spheres, and it lives in `Type` rather than an arbitrary universe so
that `Target` is a plain proposition.

- problem_id: ASmoothFourDimensionalPoincare
- collection: authored
- question_id: authored:SmoothFourDimensionalPoincare
- source: mathdb-lean
- source_locator: authored/SmoothFourDimensionalPoincare.lean#Target
- prose: The smooth four-dimensional Poincaré conjecture: every compact smooth 4-manifold homotopy equivalent to the 4-sphere is diffeomorphic to it.
- notes: Generalized Poincaré conjecture, smooth case in dimension four -- https://en.wikipedia.org/wiki/Generalized_Poincar%C3%A9_conjecture
- track: open
- answer_shape: proof
- source_category: research open
- source_ams: 57
- generator: adapters/authored/adapter.py
-/

open scoped Manifold ContDiff ContinuousMap

namespace Problem

/-- The unit sphere in `ℝ⁵`, a smooth four-manifold. -/
abbrev S4 := Metric.sphere (0 : EuclideanSpace ℝ (Fin (4 + 1))) 1

/-- The smooth Poincaré conjecture in dimension four: every compact Hausdorff smooth
4-manifold that is homotopy equivalent to the 4-sphere is diffeomorphic to it. -/
abbrev Target : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M],
    M ≃ₕ S4 → Nonempty (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ S4)

end Problem

/-!
- source_version: b80da422c1869ddababb2992c7dc83556e0f930c
-/
