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

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card

/-!
Finite-field radial projection exceptional-set conjecture (MathDB 354639).
Authored directly from the mathematical source.

- problem_id: AFiniteFieldRadialExceptions
- collection: authored
- question_id: authored:FiniteFieldRadialExceptions
- source: mathdb-lean
- source_locator: problems/354639/AFiniteFieldRadialExceptions.lean#Problem.Target
- prose: For E in a d-dimensional vector space over a finite field of order q, if q^(k-1) < |E| <= q^k with 1 <= k < d, at most 10q^k centers see fewer than |E|/10 distinct lines through E.
- notes: https://mathdb.com/p/354639/finite-field-radial-projection-exceptional-set-conjecture
- track: open
- answer_shape: proof

Reference: Lund, Pham and Thu, Radial projection theorems in finite spaces, arXiv:2205.07431v2, Conjecture 1.6 and the definition of radial projection in the introduction. https://arxiv.org/html/2205.07431v2. Compare Bright, Lund and Pham, arXiv:2311.05127v2, Theorem 1.1: https://arxiv.org/html/2311.05127v2

Radial projection here counts full affine lines through the center, not normalized Euclidean vectors. The center itself is removed before taking the image. Finset.image removes repeated lines. The exceptional condition 10 times the projection cardinality less than |E| is exactly the strict rational threshold |projection| < |E|/10; no truncated natural division is used. Every finite field is allowed, including characteristic two. The later paper arXiv:2311.05127v2 describes the conjecture as established, but its Theorem 1.1 uses constants 1/50 and 40 and assumes |E| <= q^k/100. This file retains the exact constants and size range of the MathDB question and does not claim that the later displayed theorem proves this exact target.
-/

namespace Problem

/-- Distinct full lines through `y` and a point of `E` different from `y`. -/
noncomputable def radialLines {F : Type} [Field F] {d : ℕ}
    (E : Finset (Fin d → F)) (y : Fin d → F) :
    Finset (AffineSubspace F (Fin d → F)) := by
  classical
  exact (E.erase y).image (fun x => line[F, y, x])

/-- Centers for which the number of projected lines is strictly below one tenth of `|E|`. -/
noncomputable def exceptionalCenters {F : Type} [Field F] [Fintype F] {d : ℕ}
    (E : Finset (Fin d → F)) : Finset (Fin d → F) := by
  classical
  exact Finset.univ.filter (fun y => 10 * (radialLines E y).card < E.card)

/-- Conjecture 1.6, with the field order supplied by its cardinality. -/
abbrev Target : Prop :=
  ∀ (F : Type) [Field F] [Fintype F], ∀ d k : ℕ, 1 ≤ k → k < d →
    ∀ E : Finset (Fin d → F),
      Fintype.card F ^ (k - 1) < E.card → E.card ≤ Fintype.card F ^ k →
        (exceptionalCenters E).card ≤ 10 * Fintype.card F ^ k

end Problem
