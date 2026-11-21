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
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
The distance-set dimension improvement conjecture (MathDB 377119).
Authored directly from Distance Conjecture 1.4 of Katz and Tao (2001),
rather than converted from an existing Lean statement.

- problem_id: ADistanceSetDimensionImprovement
- collection: authored
- question_id: authored:DistanceSetDimensionImprovement
- source: mathdb-lean
- source_locator: problems/377119/ADistanceSetDimensionImprovement.lean#Problem.Target
- prose: There is an absolute constant c > 0 such that every compact subset K of the
  Euclidean plane with Hausdorff dimension at least 1 has a distance set of Hausdorff
  dimension at least 1/2 + c.
- notes: https://mathdb.com/p/377119/the-distance-set-dimension-improvement-conjecture
- track: solved
- answer_shape: proof

References:
* N. H. Katz and T. Tao, "Some connections between Falconer's distance set conjecture,
  and sets of Furstenburg type" (2001), Distance Conjecture 1.4, p. 3:
  https://arxiv.org/abs/math/0101195
* T. Keleti and P. Shmerkin, "New bounds on the dimensions of planar distance sets"
  (2019), Section 1.1, equation (1.2):
  https://doi.org/10.1007/s00039-019-00500-9
  This records Bourgain's resolution using the work of Katz and Tao. The historical
  conjecture name is retained; `track: solved` refers to the literature, not a Lean proof.
-/

open MeasureTheory

namespace Problem

/-- All Euclidean distances between pairs of points of `K`, as a subset of the real line. -/
def distanceSet (K : Set (EuclideanSpace ℝ (Fin 2))) : Set ℝ :=
  Set.image2 dist K K

/-- Distance Conjecture 1.4 of Katz and Tao.

The positive real constant is chosen before `K`, so it is uniform over all compact sets.
Both dimension inequalities include equality. `dimH` takes values in `ℝ≥0∞`, so
`ENNReal.ofReal` embeds the positive real lower bound without changing its value.
The distance is the Euclidean distance, supplied by `EuclideanSpace ℝ (Fin 2)`.
-/
abbrev Target : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ K : Set (EuclideanSpace ℝ (Fin 2)),
      IsCompact K → 1 ≤ dimH K →
        ENNReal.ofReal (1 / 2 + c) ≤ dimH (distanceSet K)

end Problem
