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
import Mathlib.Analysis.Convex.Basic

/-!
Grunbaum's orthogonal line equipartition conjecture (MathDB 364279).
Authored directly from the mathematical source.

- problem_id: AGrunbaumOrthogonalPartitions
- collection: authored
- question_id: authored:GrunbaumOrthogonalPartitions
- source: mathdb-lean
- source_locator: problems/364279/AGrunbaumOrthogonalPartitions.lean#Problem.Target
- prose: Every planar convex body of area one can be partitioned by two perpendicular lines into four cyclically ordered pieces of areas t, t, 1/2-t and 1/2-t, for any t in [0,1/4].
- notes: https://mathdb.com/p/364279/grunbaum-s-orthogonal-line-equipartition-conjecture
- track: open
- answer_shape: proof

Reference: McGinnis and Zerbib, Using the KKM theorem, arXiv:2408.03921v1, Conjecture 4.2. https://arxiv.org/html/2408.03921v1

A convex body is represented by a compact convex set with nonempty interior. The lines pass through a common point and have unit orthogonal normals. The sign pairs (+,+),(-,+),(-,-),(+,-) give a cyclic order. Reversing its orientation does not change the existence statement for the pattern (t,t,s,s), since the reverse pattern is a cyclic rotation. Open quadrants omit only boundary lines of area zero. Both t=0 and t=1/4 are included. This is a positive assertion for uniform area on convex bodies, distinct from the counterexample question for arbitrary absolutely continuous measures.
-/

open MeasureTheory

namespace Problem

/-- One open quadrant, specified by its vertex and two normals. -/
def quadrant (a u v : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | 0 < inner ℝ u (x - a) ∧ 0 < inner ℝ v (x - a)}

/-- The four areas in cyclic order. Boundary lines have area zero. -/
def HasCyclicAreas (P : Set (EuclideanSpace ℝ (Fin 2))) (t : ℝ)
    (a u v : EuclideanSpace ℝ (Fin 2)) : Prop :=
  volume (P ∩ quadrant a u v) = ENNReal.ofReal t ∧
  volume (P ∩ quadrant a (-u) v) = ENNReal.ofReal t ∧
  volume (P ∩ quadrant a (-u) (-v)) = ENNReal.ofReal (1 / 2 - t) ∧
  volume (P ∩ quadrant a u (-v)) = ENNReal.ofReal (1 / 2 - t)

/-- Grunbaum's prescribed-area conjecture for convex bodies. -/
abbrev Target : Prop :=
  ∀ P : Set (EuclideanSpace ℝ (Fin 2)),
    IsCompact P → Convex ℝ P → (interior P).Nonempty → volume P = 1 →
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 4),
        ∃ a u v : EuclideanSpace ℝ (Fin 2),
          ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℝ u v = 0 ∧ HasCyclicAreas P t a u v

end Problem
