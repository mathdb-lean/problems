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

/-!
Ash-Catoiu conjecture on directional and relative Lipschitz continuity (MathDB 348867).
Authored directly from the mathematical source.

- problem_id: AAshCatoiuDirectionalLipschitz
- collection: authored
- question_id: authored:AshCatoiuDirectionalLipschitz
- source: mathdb-lean
- source_locator: problems/348867/AAshCatoiuDirectionalLipschitz.lean#Problem.Target
- prose: For any real-valued function on the Euclidean plane, let E be the points where the function is Lipschitz in every direction. The points of E where the function fails to be pointwise Lipschitz relative to E form a Lebesgue null set.
- notes: https://mathdb.com/p/348867/ash-catoiu-conjecture-on-directional-and-relative-lipschitz
- track: solved
- answer_shape: proof

Reference: Hruska, A note on directional Lipschitz continuity in the Euclidean plane, arXiv:2012.00162v2, Conjecture 1, Definition 2, and Theorem 1. https://arxiv.org/html/2012.00162v2

The function is arbitrary: no continuity or measurability is assumed. The directional bound is one-sided in the positive step h and is tested for every unit vector, including its negative. Its constants may depend on both the point and the direction. Relative Lipschitz continuity here is the pointwise bound against the fixed base point, not a two-point Lipschitz bound on a whole neighborhood. At isolated points of E the bound holds automatically. These finite local bounds are equivalent to the finite limsup definitions in the source. Nullity uses Lebesgue outer measure through Mathlib volume, so it does not require assuming E or the exceptional set Borel. The source establishes the conjecture; solved refers to the literature, not a supplied Lean proof.
-/

open MeasureTheory

namespace Problem

/-- A finite local bound along the positive ray in direction `u`. -/
def DirectionallyLipschitzAt (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x u : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧
    ∀ h : ℝ, 0 < h → h < r → |f (x + h • u) - f x| ≤ C * h

/-- Points with the directional property in every unit direction. -/
def directionalSet (f : EuclideanSpace ℝ (Fin 2) → ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → DirectionallyLipschitzAt f x u}

/-- A pointwise Lipschitz bound at `x`, tested only against nearby points of `E`. -/
def RelativelyLipschitzAt (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (E : Set (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧
    ∀ y ∈ E, dist y x < r → |f y - f x| ≤ C * dist y x

/-- The exceptional set for the relative pointwise Lipschitz property is null. -/
abbrev Target : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin 2) → ℝ,
    volume {x | x ∈ directionalSet f ∧ ¬ RelativelyLipschitzAt f (directionalSet f) x} = 0

end Problem
