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

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Alon’s question on zeros of sums of square roots (MathDB 405181).
Authored directly from the mathematical source.

- problem_id: AAlonQuadraticRadicalZeros
- collection: authored
- question_id: authored:AlonQuadraticRadicalZeros
- source: mathdb-lean
- source_locator: problems/405181/AAlonQuadraticRadicalZeros.lean#Problem.Target
- prose: A nonzero real linear combination of n square roots of everywhere positive real polynomials of degree at most two has at most 2n distinct real zeros.
- notes: https://mathdb.com/p/405181/n-alon-s-question-on-zeros-of-sums-of-square-roots-maxwell-s
- track: open
- answer_shape: proof

Reference: Binyamini, Kiro, Logunov, Novikov and Zakharov, arXiv:2609.02871v1, introduction and Theorem 1.1. https://arxiv.org/html/2609.02871v1

This uses the positive-polynomial formulation on MathDB, including constant polynomials. Not identically zero means nonzero at some real point, not merely that some coefficient is nonzero. Set.encard counts distinct zeros and also excludes an infinite zero set. The cited September 2026 preprint claims a proof; track remains open consistently with the public MathDB record pending independent review.
-/

namespace Problem

/-- A real linear combination of square roots of polynomial values. -/
noncomputable def radicalSum {n : ℕ} (c : Fin n → ℝ)
    (P : Fin n → Polynomial ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * Real.sqrt ((P i).eval x)

/-- The number of distinct real zeros is at most twice the number of summands. -/
abbrev Target : Prop :=
  ∀ n : ℕ, 0 < n → ∀ c : Fin n → ℝ, ∀ P : Fin n → Polynomial ℝ,
    (∀ i, (P i).natDegree ≤ 2) → (∀ i x, 0 < (P i).eval x) →
      (∃ x : ℝ, radicalSum c P x ≠ 0) →
        {x : ℝ | radicalSum c P x = 0}.encard ≤ (2 * n : ℕ)

end Problem
