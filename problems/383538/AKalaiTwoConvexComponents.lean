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
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Finset.Card

/-!
Kalai's Helly-type question for two-component convex sets (MathDB 383538).
Authored directly from the mathematical source.

- problem_id: AKalaiTwoConvexComponents
- collection: authored
- question_id: authored:KalaiTwoConvexComponents
- source: mathdb-lean
- source_locator: problems/383538/AKalaiTwoConvexComponents.lean#Problem.Target
- prose: In dimension d at least two, a family of n at least d+2 sets has an intersection consisting of exactly two nonempty closed convex components if every subfamily of size 1, 2, 3 or d+1 has such an intersection.
- notes: https://mathdb.com/p/383538/gil-kalai-s-helly-type-question-for-two-component-convex-set
- track: open
- answer_shape: proof

Reference: Menara, A Helly-Type Theorem for two-component convex sets, arXiv:2608.17805v1, Theorem 4.2. https://arxiv.org/html/2608.17805v1

The MathDB question uses the strengthened formulation of Theorem 4.2, not merely nonemptiness of the total intersection. Two disjoint nonempty closed convex pieces are exactly the connected components: convexity makes each connected, and each is relatively clopen in their union. No boundedness or compactness is assumed. The size-one condition includes the hypothesis on each individual set. The 2026 source claims a proof; this file supplies only its statement.
-/

namespace Problem

/-- Exactly two disjoint nonempty closed convex pieces. -/
def TwoConvexComponents {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ A B : Set (EuclideanSpace ℝ (Fin d)),
    A.Nonempty ∧ B.Nonempty ∧ IsClosed A ∧ IsClosed B ∧
      Convex ℝ A ∧ Convex ℝ B ∧ Disjoint A B ∧ S = A ∪ B

/-- The two-component intersection condition for the specified subfamily sizes. -/
abbrev Target : Prop :=
  ∀ d n : ℕ, 2 ≤ d → d + 2 ≤ n →
    ∀ F : Fin n → Set (EuclideanSpace ℝ (Fin d)),
      (∀ I : Finset (Fin n),
        I.card = 1 ∨ I.card = 2 ∨ I.card = 3 ∨ I.card = d + 1 →
          TwoConvexComponents (⋂ i ∈ I, F i)) →
        TwoConvexComponents (⋂ i, F i)

end Problem
