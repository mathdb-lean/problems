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
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
Ramos's Grunbaum-Hadwiger-Ramos mass partition conjecture (MathDB 348149).
Authored directly from the mathematical source.

- problem_id: ARamosMassPartitions
- collection: authored
- question_id: authored:RamosMassPartitions
- source: mathdb-lean
- source_locator: problems/348149/ARamosMassPartitions.lean#Problem.Target
- prose: For positive d, k and m, every family of m finite measures on R^d absolutely continuous with respect to Lebesgue measure admits an equipartition by k affine hyperplanes if and only if m(2^k-1) <= dk.
- notes: https://mathdb.com/p/348149/ramos-s-grunbaum-hadwiger-ramos-mass-partition-conjecture
- track: open
- answer_shape: proof

Reference: Roldan-Pensado and Soberon, A survey of mass partitions, arXiv:2010.00478v3, Problem 2.1.1 and Conjecture 2.1.2. https://arxiv.org/html/2010.00478v3

Each hyperplane has a unit normal and real offset. Boolean sign choices enumerate all 2^k open cells; their boundaries are null for the absolutely continuous measures. Every cell is required to be nonempty, including when all the measures are zero. Each cell must have exactly 1/2^k of each total mass. The measures need not have probability normalization. For positive k, the integer inequality is equivalent to the ceiling bound in the source, with no rounding ambiguity. Hyperplanes are not required to be orthogonal.
-/

open MeasureTheory

namespace Problem

/-- A cell specified by one choice of strict side for each hyperplane. -/
def hyperplaneCell {d k : ℕ} (u : Fin k → EuclideanSpace ℝ (Fin d))
    (a : Fin k → ℝ) (s : Fin k → Bool) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ j, if s j then inner ℝ (u j) x < a j else a j < inner ℝ (u j) x}

/-- Every family of `m` absolutely continuous finite measures has an equipartition. -/
def Admissible (d k m : ℕ) : Prop :=
  ∀ μ : Fin m → Measure (EuclideanSpace ℝ (Fin d)),
    (∀ i, IsFiniteMeasure (μ i)) → (∀ i, μ i ≪ volume) →
      ∃ u : Fin k → EuclideanSpace ℝ (Fin d), ∃ a : Fin k → ℝ,
        (∀ j, ‖u j‖ = 1) ∧ (∀ s, (hyperplaneCell u a s).Nonempty) ∧ ∀ i s,
          μ i (hyperplaneCell u a s) = μ i Set.univ / (2 : ENNReal) ^ k

/-- Ramos's necessary and conjecturally sufficient dimension bound. -/
abbrev Target : Prop :=
  ∀ d k m : ℕ, 0 < d → 0 < k → 0 < m →
    (Admissible d k m ↔ m * (2 ^ k - 1) ≤ d * k)

end Problem
