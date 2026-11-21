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
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Finset.Card

/-!
Tverberg-Vrecica conjecture (MathDB 364497).
Authored directly from the mathematical source.

- problem_id: ATverbergVrecica
- collection: authored
- question_id: authored:TverbergVrecica
- source: mathdb-lean
- source_locator: problems/364497/ATverbergVrecica.lean#Problem.Target
- prose: For k<d and k+1 finite point sets P_i in R^d of cardinality (r_i-1)(d-k+1)+1 with r_i positive, there is a common affine k-flat meeting the convex hull of every part of a partition of each P_i into r_i parts.
- notes: https://mathdb.com/p/364497/tverberg-vrecica-conjecture
- track: open
- answer_shape: proof

Reference: Sadovek and Soberon, Complex analogues of the Tverberg-Vrecica conjecture and central transversal theorems, arXiv:2408.14337v2, Conjecture 1.7 (the real conjecture). https://arxiv.org/html/2408.14337v2

A label function on each finite point set specifies its partition. The fibers are disjoint and cover the point set; the required convex-hull intersections force every part to be nonempty. Labels outside P_i have no effect and can be extended arbitrarily because r_i is positive. One shared affine subspace is chosen for all partitions. Its dimension is the dimension of its direction subspace. The parameters range over all positive r_i, without prime-power restrictions.
-/

namespace Problem

/-- The real Tverberg-Vrecica conjecture, with partitions encoded by labels. -/
abbrev Target : Prop :=
  ∀ d k : ℕ, k < d → ∀ r : Fin (k + 1) → ℕ, (∀ i, 0 < r i) →
    ∀ P : Fin (k + 1) → Finset (EuclideanSpace ℝ (Fin d)),
      (∀ i, (P i).card = (r i - 1) * (d - k + 1) + 1) →
        ∃ V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
          (V : Set (EuclideanSpace ℝ (Fin d))).Nonempty ∧
          Module.finrank ℝ V.direction = k ∧
          ∃ c : ∀ i : Fin (k + 1), EuclideanSpace ℝ (Fin d) → Fin (r i),
            ∀ i j, (convexHull ℝ {x | x ∈ P i ∧ c i x = j} ∩
              (V : Set (EuclideanSpace ℝ (Fin d)))).Nonempty

end Problem
