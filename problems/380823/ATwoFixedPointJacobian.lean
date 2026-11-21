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
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
The two-fixed-point Jacobian eigenvalue conjecture (MathDB 380823).
Authored directly from the mathematical source.

- problem_id: ATwoFixedPointJacobian
- collection: authored
- question_id: authored:TwoFixedPointJacobian
- source: mathdb-lean
- source_locator: problems/380823/ATwoFixedPointJacobian.lean#Problem.Target
- prose: If a continuously differentiable self-map of a positive-dimensional real Euclidean space has two distinct fixed points, its Jacobian has a nonzero complex eigenvalue at some point.
- notes: https://mathdb.com/p/380823/the-two-fixed-point-jacobian-eigenvalue-conjecture
- track: open
- answer_shape: proof

Reference: Campbell, Unipotent Jacobian Matrices and Univalent Maps, arXiv:math/9907157v2, Conjecture 6. https://arxiv.org/pdf/math/9907157

The Jacobian is formed by applying the real Frechet derivative to the standard basis vectors. Eigenvalues are complex, even though the map and derivative are real. A root of the characteristic polynomial is exactly a complex eigenvalue. The point witnessing a nonzero eigenvalue need not be a fixed point. ContDiff of order one ensures the derivative is defined at every point, so the fallback value of fderiv outside differentiability is irrelevant.
-/

namespace Problem

/-- The real Jacobian in the standard basis, with entries included in the complex numbers. -/
noncomputable def complexJacobian {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ((fderiv ℝ f x (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) i : ℂ)

/-- A pair of distinct fixed points forces a nonzero eigenvalue somewhere. -/
abbrev Target : Prop :=
  ∀ n : ℕ, 0 < n →
    ∀ f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContDiff ℝ 1 f →
      (∃ a b, a ≠ b ∧ f a = a ∧ f b = b) →
        ∃ x : EuclideanSpace ℝ (Fin n), ∃ z : ℂ,
          z ≠ 0 ∧ (complexJacobian f x).charpoly.eval z = 0

end Problem
