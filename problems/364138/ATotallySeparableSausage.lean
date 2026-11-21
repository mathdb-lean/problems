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
import Mathlib.Analysis.Convex.Hull

/-!
Fejes Toth's sausage conjecture for totally separable unit-ball packings (MathDB 364138).
Authored directly from the mathematical source.

- problem_id: ATotallySeparableSausage
- collection: authored
- question_id: authored:TotallySeparableSausage
- source: mathdb-lean
- source_locator: problems/364138/ATotallySeparableSausage.lean#Problem.Target
- prose: For 3 <= d <= 41 and N > 1, the convex hull of a totally separable packing of N unit balls has volume at least that of N consecutively tangent collinear unit balls.
- notes: https://mathdb.com/p/364138/fejes-toth-s-sausage-conjecture-for-ts-packings-of-unit-ball
- track: open
- answer_shape: proof

Reference: Bezdek and Langi, On separability in discrete geometry, arXiv:2407.20169v2, Definition 14 and Conjecture 3. https://arxiv.org/html/2407.20169v2

For every ordered pair of distinct balls, a unit normal and offset specify a separating hyperplane avoiding the interior of every ball. The unit-normal inequalities express distances at least one from this hyperplane, allowing tangency. They also force distinct centers and non-overlapping interiors. The comparison packing has centers 2*i*u for a unit vector u, so adjacent balls touch and the center segment has length 2(N-1). Quantifying all unit vectors avoids selecting a coordinate axis and gives the same comparison volume by rotation invariance.
-/

open MeasureTheory

namespace Problem

/-- Every pair is separated by a hyperplane avoiding every open unit ball. -/
def TotallySeparable {d N : ℕ} (c : Fin N → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ i j, i ≠ j → ∃ u : EuclideanSpace ℝ (Fin d), ∃ a : ℝ,
    ‖u‖ = 1 ∧ inner ℝ u (c i) + 1 ≤ a ∧ a ≤ inner ℝ u (c j) - 1 ∧
      ∀ k, 1 ≤ |inner ℝ u (c k) - a|

/-- The convex hull of the union of the closed unit balls. -/
def packingHull {d N : ℕ} (c : Fin N → EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  convexHull ℝ (⋃ i, Metric.closedBall (c i) 1)

/-- The conjecture in precisely the remaining dimension range stated in MathDB. -/
abbrev Target : Prop :=
  ∀ d N : ℕ, 3 ≤ d → d ≤ 41 → 1 < N →
    ∀ c : Fin N → EuclideanSpace ℝ (Fin d), TotallySeparable c →
      ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
        volume (packingHull (fun i : Fin N => (2 * (i.val : ℝ)) • u)) ≤
          volume (packingHull c)

end Problem
