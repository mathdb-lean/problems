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
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
Dyn–Farkhi conjecture on Hausdorff convexification under Minkowski addition (MathDB 375200).
Authored directly from the mathematical source.

- problem_id: ADynFarkhiConvexification
- collection: authored
- question_id: authored:DynFarkhiConvexification
- source: mathdb-lean
- source_locator: problems/375200/ADynFarkhiConvexification.lean#Problem.Target
- prose: The general Dyn-Farkhi assertion is false: there are nonempty compact sets A and B in some positive-dimensional Euclidean space for which the squared Hausdorff distance of A+B from its convex hull exceeds the sum of the corresponding squared distances for A and B.
- notes: https://mathdb.com/p/375200/dyn-farkhi-conjecture-on-hausdorff-convexification-under-min
- track: solved
- answer_shape: proof

Reference: Van Hintum, arXiv:2606.10815v1, introduction and Conjecture 1.1 (historical assertion). The introduction records the disproof in dimensions at least 3 by Fradelizi, Madiman, Marsiglietti and Zvavitch. https://arxiv.org/html/2606.10815v1

The original universal assertion is recorded separately as Conjecture. Target asks for its negation because the statement is disproved in the literature. For a nonempty compact set, its convex hull is compact in finite-dimensional Euclidean space. Since the set is contained in its convex hull, the symmetric Hausdorff distance is exactly the one-sided sup-inf quantity used in the source. All distances are Euclidean.
-/

namespace Problem

/-- Hausdorff distance from a set to its convex hull. -/
noncomputable def convexityDefect {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  Metric.hausdorffDist A (convexHull ℝ A)

/-- The original Dyn–Farkhi inequality in all positive dimensions. -/
abbrev Conjecture : Prop :=
  ∀ n : ℕ, 0 < n →
    ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      A.Nonempty → IsCompact A → B.Nonempty → IsCompact B →
        convexityDefect (Set.image2 (· + ·) A B) ^ 2 ≤
          convexityDefect A ^ 2 + convexityDefect B ^ 2

/-- Disprove the general assertion; its low-dimensional cases do not settle this target. -/
abbrev Target : Prop := ¬ Conjecture

end Problem
