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

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
Barany's conjecture on uneven orthogonal mass partitions (MathDB 405456).
Authored directly from the mathematical source.

- problem_id: AUnevenOrthogonalMassPartitions
- collection: authored
- question_id: authored:UnevenOrthogonalMassPartitions
- source: mathdb-lean
- source_locator: problems/405456/AUnevenOrthogonalMassPartitions.lean#Problem.Target
- prose: There are an absolutely continuous planar probability measure and t in (0,1/4) for which no two perpendicular lines give cyclic region masses t,t,1/2-t,1/2-t.
- notes: https://mathdb.com/p/405456/barany-s-conjecture-on-uneven-orthogonal-mass-partitions
- track: open
- answer_shape: proof

Reference: Martinez-Sandoval, Counterexamples and symmetry for uneven orthogonal mass partitions in the plane, arXiv:2609.16757v1, Problem 1.2 and Theorem 1.4. https://arxiv.org/html/2609.16757v1

This is the existence of a counterexample stated on MathDB, not the opposite universal partition assertion. The cited recent preprint claims this negative answer; no proof is supplied here. Unit orthogonal normals describe every pair of perpendicular affine lines through their common intersection. The four quadrants are listed cyclically. All rotations and reversals of the cyclic order are covered by quantifying over all ordered orthonormal pairs. Open quadrants are valid because absolute continuity makes every boundary line null.
-/

open MeasureTheory

namespace Problem

/-- One open quadrant determined by a center and two perpendicular normals. -/
def quadrant (a u v : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | 0 < inner ℝ u (x - a) ∧ 0 < inner ℝ v (x - a)}

/-- The prescribed masses in the cyclic order `(+,+),(-,+),(-,-),(+,-)`. -/
def HasCyclicMasses (μ : Measure (EuclideanSpace ℝ (Fin 2))) (t : ℝ)
    (a u v : EuclideanSpace ℝ (Fin 2)) : Prop :=
  μ (quadrant a u v) = ENNReal.ofReal t ∧
  μ (quadrant a (-u) v) = ENNReal.ofReal t ∧
  μ (quadrant a (-u) (-v)) = ENNReal.ofReal (1 / 2 - t) ∧
  μ (quadrant a u (-v)) = ENNReal.ofReal (1 / 2 - t)

/-- Some absolutely continuous mass has no orthogonal partition with these proportions. -/
abbrev Target : Prop :=
  ∃ μ : Measure (EuclideanSpace ℝ (Fin 2)), IsProbabilityMeasure μ ∧ μ ≪ volume ∧
    ∃ t ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ a u v : EuclideanSpace ℝ (Fin 2),
        ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 → ¬ HasCyclicMasses μ t a u v

end Problem
