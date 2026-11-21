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

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-!
Hausdorff-dimensional packing conjecture for special-linear symmetries (MathDB 366503).
Authored directly from the mathematical source.

- problem_id: ASpecialLinearSymmetries
- collection: authored
- question_id: authored:SpecialLinearSymmetries
- source: mathdb-lean
- source_locator: problems/366503/ASpecialLinearSymmetries.lean#Problem.Target
- prose: A compact planar set E is contained in a line if a family R of determinant-one linear symmetries preserving E has Hausdorff dimension greater than three halves of the Hausdorff dimension of E.
- notes: https://mathdb.com/p/366503/hausdorff-dimensional-packing-conjecture-for-special-linear
- track: open
- answer_shape: proof

Reference: Hung, Pham and Slavov, arXiv:2501.01697v2, Conjecture 1.8. https://arxiv.org/html/2501.01697v2

R is an arbitrary set of special-linear matrices; it is not required to be a subgroup. Its dimension is computed after inclusion in the space of real 2-by-2 matrices. The product metric there is bi-Lipschitz equivalent to the Euclidean metric on four entries, giving the same Hausdorff dimension. The conclusion is containment in a full affine line.
-/

open MeasureTheory

namespace Problem

open scoped Matrix.Norms.Elementwise

/-- The usual matrix action on the Euclidean plane. -/
def matrixAction (M : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i => ∑ j, M i j * x j)

/-- Conjecture 1.8; the symmetry family has no regularity or group assumption. -/
abbrev Target : Prop :=
  ∀ E : Set (EuclideanSpace ℝ (Fin 2)), IsCompact E →
    ∀ R : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (∀ M ∈ R, matrixAction M '' E = E) →
      (3 / 2 : ENNReal) * dimH E <
        dimH ((fun M : Matrix.SpecialLinearGroup (Fin 2) ℝ =>
          (M : Matrix (Fin 2) (Fin 2) ℝ)) '' R) →
      ∃ a b : EuclideanSpace ℝ (Fin 2), a ≠ b ∧
        E ⊆ (line[ℝ, a, b] : Set (EuclideanSpace ℝ (Fin 2)))

end Problem
