/-
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

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Perfect

/-!
The full-measure universality and strongly meager sets conjecture (MathDB 366243).
Authored directly from the mathematical source.

- problem_id: AFullMeasureStrongMeagerness
- collection: authored
- question_id: authored:FullMeasureStrongMeagerness
- source: mathdb-lean
- source_locator: problems/366243/AFullMeasureStrongMeagerness.lean#Problem.Target
- prose: A real set is full-measure universal exactly when it is strongly meager; moreover, no nonempty perfect real set is full-measure universal.
- notes: https://mathdb.com/p/366243/the-full-measure-universality-and-strongly-meager-sets-conje
- track: open
- answer_shape: proof

Reference: Jung, Lai and Mooroogen, Fifty years of the Erdos similarity conjecture, arXiv:2412.11062v2, Conjecture 4.3(1)-(2). https://arxiv.org/html/2412.11062v2

Both assertions on the MathDB page are included as a conjunction. Null sets and full-measure sets need not be Borel. Affine scale is nonzero. Nonemptiness of the perfect set is an explicit interpretation of the source: the empty set is Perfect in Mathlib and is trivially full-measure universal, so the non-universality assertion cannot include it. The source does not explicitly state this convention. No countability or measurability assumption is imposed on the arbitrary set X.
-/

open MeasureTheory

namespace Problem

/-- Universality for all sets whose complement has Lebesgue measure zero. -/
def FullMeasureUniversal (X : Set ℝ) : Prop :=
  ∀ E : Set ℝ, volume Eᶜ = 0 →
    ∃ a b : ℝ, a ≠ 0 ∧ (fun x => a * x + b) '' X ⊆ E

/-- No sum with a Lebesgue-null set covers the real line. -/
def StronglyMeager (X : Set ℝ) : Prop :=
  ∀ M : Set ℝ, volume M = 0 → Set.image2 (· + ·) X M ≠ Set.univ

/-- Both parts of Conjecture 4.3. -/
abbrev Target : Prop :=
  (∀ X : Set ℝ, FullMeasureUniversal X ↔ StronglyMeager X) ∧
    (∀ P : Set ℝ, P.Nonempty → Perfect P → ¬ FullMeasureUniversal P)

end Problem
