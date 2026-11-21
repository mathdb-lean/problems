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

import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
The shifted-product nonempty-interior conjecture for product sets (MathDB 375707).
Authored directly from the mathematical source.

- problem_id: AShiftedProductInterior
- collection: authored
- question_id: authored:ShiftedProductInterior
- source: mathdb-lean
- source_locator: problems/375707/AShiftedProductInterior.lean#Problem.Target
- prose: For each integer n at least 3 there is a positive epsilon such that every Borel subset A of the real line of Hausdorff dimension greater than 2/n - epsilon admits n real shifts whose setwise product contains a nonempty open interval.
- notes: https://mathdb.com/p/375707/the-shifted-product-nonempty-interior-conjecture-for-product
- track: open
- answer_shape: proof

Reference: Hong, Liang and Shen, arXiv:2607.00372v1, Conjecture 1.7. https://arxiv.org/html/2607.00372v1

The epsilon depends only on n, and is chosen before A. MeasurableSet on the real line means Borel. All factors may choose their points of A independently. Hausdorff dimension of a subset of the real line is finite, so toReal is its ordinary real-valued dimension; it does not discard infinity here.
-/

open MeasureTheory

namespace Problem

/-- Products with one independently chosen point of `A` in each shifted factor. -/
def shiftedProduct {n : ℕ} (A : Set ℝ) (t : Fin n → ℝ) : Set ℝ :=
  {y | ∃ x : Fin n → ℝ, (∀ i, x i ∈ A) ∧ y = ∏ i, (t i + x i)}

/-- Conjecture 1.7, with an improvement uniform over all Borel sets `A`. -/
abbrev Target : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∃ ε : ℝ, 0 < ε ∧
    ∀ A : Set ℝ, MeasurableSet A →
      2 / (n : ℝ) - ε < (dimH A).toReal →
        ∃ t : Fin n → ℝ, ∃ a b : ℝ,
          a < b ∧ Set.Ioo a b ⊆ shiftedProduct A t

end Problem
