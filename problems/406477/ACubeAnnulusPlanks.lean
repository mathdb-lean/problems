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
Cube-annulus plank-covering conjecture (MathDB 406477).
Authored directly from the mathematical source.

- problem_id: ACubeAnnulusPlanks
- collection: authored
- question_id: authored:CubeAnnulusPlanks
- source: mathdb-lean
- source_locator: problems/406477/ACubeAnnulusPlanks.lean#Problem.Target
- prose: In dimension d >= 2, if 0 < delta < 1 and delta <= 1 - 1/d, every finite plank cover of the centered unit cube minus the concentric closed cube of side delta has total width at least one.
- notes: https://mathdb.com/p/406477/cube-annulus-plank-covering-conjecture
- track: open
- answer_shape: proof

Reference: Ambrus, Corbo, Goto, Leitz and Mawhinney, On plank coverings of cube annuli, arXiv:2610.18770v1, Conjecture 1.2. https://arxiv.org/html/2610.18770v1

The centered annulus matches the MathDB formulation. The primary source conjectures a stronger assertion allowing off-center holes as well. The unit normal and ordered boundary levels make b-a the Euclidean width. Removing a closed hole or its interior is equivalent for finite closed plank coverings by taking closure. The dimension-dependent threshold uses real division, not natural-number subtraction or division. A later preprint arXiv:2611.00379 claims a stronger covering theorem; the public MathDB record remains open.
-/

namespace Problem

/-- A closed Euclidean plank, with unit-normal and positive-width conditions in the target. -/
def plank {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (a b : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | a ≤ inner ℝ u x ∧ inner ℝ u x ≤ b}

/-- The centered cube annulus of outer side one and inner side `δ`. -/
def cubeAnnulus (d : ℕ) (δ : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ j, x j ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)} \
    {x | ∀ j, x j ∈ Set.Icc (-δ / 2) (δ / 2)}

/-- The threshold `δ ≤ 1 - 1/d` forces total covering width at least one. -/
abbrev Target : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ δ : ℝ, 0 < δ → δ < 1 → δ ≤ 1 - 1 / (d : ℝ) →
    ∀ N : ℕ, ∀ u : Fin N → EuclideanSpace ℝ (Fin d), ∀ a b : Fin N → ℝ,
      (∀ i, ‖u i‖ = 1) → (∀ i, a i < b i) →
        cubeAnnulus d δ ⊆ (⋃ i, plank (u i) (a i) (b i)) →
          1 ≤ ∑ i, (b i - a i)

end Problem
