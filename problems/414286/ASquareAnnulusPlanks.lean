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

/-!
Bezdek’s plank-covering conjecture for square annuli (MathDB 414286).
Authored directly from the mathematical source.

- problem_id: ASquareAnnulusPlanks
- collection: authored
- question_id: authored:SquareAnnulusPlanks
- source: mathdb-lean
- source_locator: problems/414286/ASquareAnnulusPlanks.lean#Problem.Target
- prose: Every finite covering of the unit square minus its concentric closed square of side one half by Euclidean planks has total width at least one.
- notes: https://mathdb.com/p/414286/bezdek-s-plank-covering-conjecture-for-square-annuli
- track: open
- answer_shape: proof

Reference: Bakaev and Polyanskii, A sharp plank theorem for cube annuli, arXiv:2611.00379v1, introduction and Theorem 1. https://arxiv.org/html/2611.00379v1

This states the concentric square formulation on MathDB; the cited paper treats more general hole locations. A plank is a closed strip with a unit normal and distinct boundary levels, so its width is exactly b-a. The hole is closed as written on MathDB. For finite unions of closed planks, including or excluding the inner boundary gives equivalent covering assertions by taking closure. A recent preprint claims a proof; no Lean proof or independent verification is claimed here.
-/

namespace Problem

/-- The closed strip between two levels of a linear functional with unit normal. -/
def plank (u : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | a ≤ inner ℝ u x ∧ inner ℝ u x ≤ b}

/-- The unit square with the concentric closed half-side square removed. -/
def squareAnnulus : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∀ j, x j ∈ Set.Icc 0 1} \ {x | ∀ j, x j ∈ Set.Icc (1 / 4 : ℝ) (3 / 4)}

/-- Every finite plank cover has total Euclidean width at least one. -/
abbrev Target : Prop :=
  ∀ N : ℕ, ∀ u : Fin N → EuclideanSpace ℝ (Fin 2), ∀ a b : Fin N → ℝ,
    (∀ i, ‖u i‖ = 1) → (∀ i, a i < b i) →
      squareAnnulus ⊆ (⋃ i, plank (u i) (a i) (b i)) →
        1 ≤ ∑ i, (b i - a i)

end Problem
