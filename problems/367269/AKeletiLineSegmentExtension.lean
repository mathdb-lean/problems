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

import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
Keleti's line segment extension conjecture (MathDB 367269).
Authored directly from the mathematical sources, rather than converted from an
existing Lean statement.

- problem_id: AKeletiLineSegmentExtension
- collection: authored
- question_id: authored:KeletiLineSegmentExtension
- source: mathdb-lean
- source_locator: problems/367269/AKeletiLineSegmentExtension.lean#Problem.Target
- prose: In every positive dimension, extending an arbitrary family of positive-length
  line segments in Euclidean space to their containing full lines preserves the Hausdorff
  dimension of their union.
- notes: https://mathdb.com/p/367269/keleti-s-line-segment-extension-conjecture
- track: open
- answer_shape: proof

References:
* T. Keleti, "Are lines much bigger than line segments?", Conjecture 1.1:
  https://arxiv.org/abs/1409.5992
* H. Wang and J. Zahl, "Volume estimates for unions of convex sets, and the Kakeya set
  conjecture in three dimensions", Section 1.6, Conjecture 1.13:
  https://arxiv.org/html/2502.17655v1#S1.SS6
  Theorem 1.14 establishes the three-dimensional case. This target is the statement
  in all positive dimensions, not just that solved case.

Endpoint pairs encode closed segments. No finiteness, countability, boundedness or
measurability condition is imposed on the family or its union. Reversing an endpoint
pair or representing the same geometric segment more than once does not change either union.
The closed-segment formulation also implies the version allowing open or half-open segments:
choose a nondegenerate closed subsegment of each segment. The full lines are unchanged,
and monotonicity of Hausdorff dimension sandwiches the original union between the union
of these subsegments and the union of the full lines. The converse is immediate.
-/

open MeasureTheory

namespace Problem

/-- The union of the closed segments represented by the endpoint pairs in `L`. -/
def segmentUnion {n : ℕ}
    (L : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  ⋃ p ∈ L, affineSegment ℝ p.1 p.2

/-- The union of the full affine lines through the endpoint pairs in `L`.
The target requires distinct endpoints, so each affine span is a line rather than a point. -/
def lineUnion {n : ℕ}
    (L : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  ⋃ p ∈ L, (line[ℝ, p.1, p.2] : Set (EuclideanSpace ℝ (Fin n)))

/-- Keleti's line segment extension conjecture for arbitrary families in every positive
dimension. Distinct endpoints express positive length; `L` may be uncountable or empty. -/
abbrev Target : Prop :=
  ∀ n : ℕ, 0 < n →
    ∀ L : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      (∀ p ∈ L, p.1 ≠ p.2) →
        dimH (lineUnion L) = dimH (segmentUnion L)

end Problem
