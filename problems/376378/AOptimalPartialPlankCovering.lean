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

/-!
The optimal partial plank covering conjecture for convex bodies (MathDB 376378).
Authored directly from the mathematical source.

- problem_id: AOptimalPartialPlankCovering
- collection: authored
- question_id: authored:OptimalPartialPlankCovering
- source: mathdb-lean
- source_locator: problems/376378/AOptimalPartialPlankCovering.lean#Problem.Target
- prose: For every positive-dimensional convex body K and total width W > 0, a single plank of width W covers at least as much of K as any finite family of planks whose widths sum to W.
- notes: https://mathdb.com/p/376378/the-optimal-partial-plank-covering-conjecture-for-convex-bod
- track: open
- answer_shape: proof

Reference: Bakaev and Polyanskii, Optimal partial plank coverings, arXiv:2607.27483v1, Conjecture 1. https://arxiv.org/html/2607.27483v1

The optimal single plank is chosen before the competing finite family and depends only on K and W. The source defines a convex body as compact and convex with nonempty interior. Unit normals make b-a the Euclidean width. Competing widths are strictly positive and sum exactly to W. Closed planks cause no boundary ambiguity for Lebesgue volume. The paper proves the ball and planar cases; this target includes all positive dimensions.
-/

open MeasureTheory

namespace Problem

/-- Closed plank; for a unit normal and `a < b`, its width is `b - a`. -/
def plank {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (a b : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | a ≤ inner ℝ u x ∧ inner ℝ u x ≤ b}

/-- A single optimal plank dominates every finite covering family of the same total width. -/
abbrev Target : Prop :=
  ∀ d : ℕ, 0 < d → ∀ K : Set (EuclideanSpace ℝ (Fin d)),
    IsCompact K → Convex ℝ K → (interior K).Nonempty → ∀ W : ℝ, 0 < W →
      ∃ u : EuclideanSpace ℝ (Fin d), ∃ a : ℝ, ‖u‖ = 1 ∧
        ∀ N : ℕ, ∀ v : Fin N → EuclideanSpace ℝ (Fin d), ∀ b c : Fin N → ℝ,
          (∀ i, ‖v i‖ = 1) → (∀ i, b i < c i) → (∑ i, (c i - b i)) = W →
            volume (K ∩ ⋃ i, plank (v i) (b i) (c i)) ≤
              volume (K ∩ plank u a (a + W))

end Problem
