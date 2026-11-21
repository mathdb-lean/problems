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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
The logarithmic Brunn-Minkowski conjecture for origin-symmetric convex bodies (MathDB 373243).
Authored directly from the mathematical source.

- problem_id: ALogarithmicBrunnMinkowski
- collection: authored
- question_id: authored:LogarithmicBrunnMinkowski
- source: mathdb-lean
- source_locator: problems/373243/ALogarithmicBrunnMinkowski.lean#Problem.Target
- prose: For origin-symmetric compact convex bodies K and L in positive-dimensional Euclidean space with the origin in their interiors, the Wulff body of the geometric interpolation of their support functions has volume at least vol(K)^t vol(L)^(1-t), for every t in [0,1].
- notes: https://mathdb.com/p/373243/the-logarithmic-brunn-minkowski-conjecture-for-origin-symmet
- track: open
- answer_shape: proof

Reference: Iffland, The local logarithmic Brunn-Minkowski inequality for bodies of revolution, arXiv:2602.17912v1, Conjecture 1.1 and the preceding Wulff-shape definition. https://arxiv.org/html/2602.17912v1

The logarithmic combination is an intersection of supporting halfspaces, not the pointwise product or Minkowski sum of bodies. Unit normals use the Euclidean norm. Support values are finite and positive under the compactness and interior hypotheses. Volume is Mathlib Lebesgue measure in Euclidean space, with real powers in ENNReal; all relevant body volumes are finite. Origin symmetry is expressed pointwise by x in K iff -x in K. MathDB records an unverified 2026 solution claim; this contribution states the conjecture and does not endorse a proof.
-/

open MeasureTheory

namespace Problem

/-- Support value in direction `u`; finite for a nonempty compact body. -/
noncomputable def supportValue {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun x => inner ℝ u x) '' K)

/-- The Wulff body of the geometric mean of the two support functions. -/
def logCombination {n : ℕ} (K L : Set (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 →
    inner ℝ u x ≤ (supportValue K u) ^ t * (supportValue L u) ^ (1 - t)}

/-- The global logarithmic Brunn-Minkowski inequality. -/
abbrev Target : Prop :=
  ∀ n : ℕ, 0 < n → ∀ K L : Set (EuclideanSpace ℝ (Fin n)),
    IsCompact K → Convex ℝ K → (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K →
    (∀ x, x ∈ K ↔ -x ∈ K) →
    IsCompact L → Convex ℝ L → (0 : EuclideanSpace ℝ (Fin n)) ∈ interior L →
    (∀ x, x ∈ L ↔ -x ∈ L) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (volume K) ^ t * (volume L) ^ (1 - t) ≤ volume (logCombination K L t)

end Problem
