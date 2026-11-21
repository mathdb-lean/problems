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
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Data.Finset.Card

/-!
All-even sets in R3 conjecture (MathDB 414217).
Authored directly from the mathematical source.

- problem_id: ALineAllEvenThreeSpace
- collection: authored
- question_id: authored:LineAllEvenThreeSpace
- source: mathdb-lean
- source_locator: problems/414217/ALineAllEvenThreeSpace.lean#Problem.Target
- prose: If a finite nonempty set in Euclidean three-space meets an even number of parallel lines in every direction, its affine span is not the whole space.
- notes: https://mathdb.com/p/414217/all-even-sets-in-r3-conjecture
- track: open
- answer_shape: proof

Reference: Kalmanovich and Nivasch, All-even sets in R2 and R3, arXiv:2610.38864v1, Section 2, Conjecture 2.1. https://arxiv.org/html/2610.38864v1

The MathDB title says all-even, but its statement is the stronger line-all-even conjecture, as distinguished in the source. Every nonzero vector represents a direction; the affine line through p and p+v is the unique line in that direction through p. Finset.image removes repetitions, so a line meeting several points is counted once. The conclusion uses Mathlib affineSpan. This is the contrapositive of the primary source formulation with an odd line direction.
-/

namespace Problem

/-- Distinct lines parallel to `v` that meet the finite point set. -/
noncomputable def parallelLines (S : Finset (EuclideanSpace ℝ (Fin 3)))
    (v : EuclideanSpace ℝ (Fin 3)) :
    Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))) := by
  classical
  exact S.image (fun p => line[ℝ, p, p + v])

/-- The line-all-even conjecture; directions are represented by nonzero vectors. -/
abbrev Target : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 3)), S.Nonempty →
    (∀ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 → Even (parallelLines S v).card) →
      affineSpan ℝ (S : Set (EuclideanSpace ℝ (Fin 3))) ≠ ⊤

end Problem
