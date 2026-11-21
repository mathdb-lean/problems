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
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Eval

/-!
Kroo's homogeneous polynomial approximation conjecture (MathDB 414215).
Authored directly from the mathematical source.

- problem_id: AKrooHomogeneousApproximation
- collection: authored
- question_id: authored:KrooHomogeneousApproximation
- source: mathdb-lean
- source_locator: problems/414215/AKrooHomogeneousApproximation.lean#Problem.Target
- prose: Every continuous real function on the boundary of an origin-symmetric convex body can be uniformly approximated by sums of two homogeneous polynomials of consecutive degrees n and n+1, with arbitrarily small error for every sufficiently large n.
- notes: https://mathdb.com/p/414215/kroo-s-homogeneous-polynomial-approximation-conjecture
- track: open
- answer_shape: proof

Reference: Kroo, Homogeneous polynomial approximation on convex and star like domains, Dolomites Research Notes on Approximation 16 (2023), Section 5, Problem 1. https://drna.padovauniversitypress.it/system/files/papers/KrooSurvey2023.pdf

The function is defined only on the boundary, via a ContinuousMap from its subtype. The epsilon formulation requires an approximating pair for every sufficiently large degree, not just some arbitrarily large degrees. Mathlib IsHomogeneous permits the zero polynomial, as does the homogeneous polynomial vector space in the source. Polynomial evaluation uses the ordinary real coordinates of Euclidean space. MathDB records a recent claimed solution; this is only a formal statement.
-/

namespace Problem

/-- Uniform approximation on the boundary by two consecutive homogeneous degrees. -/
abbrev Target : Prop :=
  ∀ d : ℕ, 0 < d → ∀ K : Set (EuclideanSpace ℝ (Fin d)),
    IsCompact K → Convex ℝ K → (interior K).Nonempty →
    (∀ x, x ∈ K ↔ -x ∈ K) → ∀ f : C(↥(frontier K), ℝ),
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ P Q : MvPolynomial (Fin d) ℝ,
          P.IsHomogeneous n ∧ Q.IsHomogeneous (n + 1) ∧
            ∀ x : ↥(frontier K),
              |MvPolynomial.eval (fun i => x.val i) P +
                MvPolynomial.eval (fun i => x.val i) Q - f x| < ε

end Problem
