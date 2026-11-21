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

/-!
Full measure universality conjecture (MathDB 365068).
Authored directly from the mathematical source.

- problem_id: AFullMeasureUniversality
- collection: authored
- question_id: authored:FullMeasureUniversality
- source: mathdb-lean
- source_locator: problems/365068/AFullMeasureUniversality.lean#Problem.Target
- prose: Every subset of the real line that has an affine copy with nonzero scale in every set with null complement is countable.
- notes: https://mathdb.com/p/365068/full-measure-universality-conjecture
- track: open
- answer_shape: proof

Reference: Jung and Lai, arXiv:2410.01275v2, Definition 4.1 and Conjecture 4.2. https://arxiv.org/html/2410.01275v2

Full measure means a null complement, not infinite measure. A set with null complement is Lebesgue measurable in the completion, so no Borel restriction is imposed. The scale may be negative but may not be zero. X has no measurability assumption. The source discusses set-theoretic independence; this is a statement, not a claimed theorem of Lean.
-/

open MeasureTheory

namespace Problem

/-- Every set with null complement contains a nondegenerate affine copy of `X`. -/
def FullMeasureUniversal (X : Set ℝ) : Prop :=
  ∀ E : Set ℝ, volume Eᶜ = 0 →
    ∃ a b : ℝ, a ≠ 0 ∧ (fun x => a * x + b) '' X ⊆ E

/-- There are no uncountable full-measure universal subsets of the real line. -/
abbrev Target : Prop :=
  ∀ X : Set ℝ, FullMeasureUniversal X → X.Countable

end Problem
