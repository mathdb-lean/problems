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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Conjecture on the monotonicity of Riemann sums for reciprocal quadratics (MathDB 360607).
Authored directly from the mathematical source.

- problem_id: AReciprocalQuadraticRiemannSums
- collection: authored
- question_id: authored:ReciprocalQuadraticRiemannSums
- source: mathdb-lean
- source_locator: problems/360607/AReciprocalQuadraticRiemannSums.lean#Problem.Target
- prose: For f_b(x)=1/(1-bx+x^2), the left Riemann sums are neither nondecreasing nor nonincreasing for 1/2 < b < 1, and are nondecreasing for beta < b <= 2. The right sums are neither nondecreasing nor nonincreasing for 1 < b < 3/2, and are nonincreasing for beta < b < 2, where beta=(3+sqrt(13))/4.
- notes: https://mathdb.com/p/360607/conjecture-on-the-monotonicity-of-riemann-sums-for-reciproca
- track: open
- answer_shape: proof

Reference: Ludovick Bouthat, On the monotonicity of left and right Riemann sums, arXiv:2311.01208v2, Conjecture 3.2 and definitions in Section 1.1. https://arxiv.org/html/2311.01208v2

All four assertions in Conjecture 3.2 are included. Lean index n denotes the sum on n+1 equal subintervals, so Monotone and Antitone range over every positive subdivision count. The left sum omits x=1 and includes x=0; the right sum does the reverse. The singular parameter b=2 occurs only in the left-sum assertion, so no evaluation at its pole is used. The source leaves Conjecture 3.2 open except for its left-sum endpoint b=2.
-/

namespace Problem

/-- The reciprocal quadratic whose uniform Riemann sums are being studied. -/
noncomputable def reciprocalQuadratic (b x : ℝ) : ℝ := 1 / (1 - b * x + x ^ 2)

/-- Left sum on `n+1` subintervals of `[0,1]`. -/
noncomputable def leftSum (b : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), reciprocalQuadratic b ((k : ℝ) / ((n : ℝ) + 1))) /
    ((n : ℝ) + 1)

/-- Right sum on `n+1` subintervals of `[0,1]`. -/
noncomputable def rightSum (b : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1),
    reciprocalQuadratic b (((k : ℝ) + 1) / ((n : ℝ) + 1))) / ((n : ℝ) + 1)

/-- The critical parameter from the source. -/
noncomputable def beta : ℝ := (3 + Real.sqrt 13) / 4

/-- All parts of Conjecture 3.2, with their distinct parameter intervals. -/
abbrev Target : Prop :=
  (∀ b ∈ Set.Ioo (1 / 2 : ℝ) 1, ¬ Monotone (leftSum b) ∧ ¬ Antitone (leftSum b)) ∧
  (∀ b ∈ Set.Ioc beta 2, Monotone (leftSum b)) ∧
  (∀ b ∈ Set.Ioo (1 : ℝ) (3 / 2), ¬ Monotone (rightSum b) ∧ ¬ Antitone (rightSum b)) ∧
  (∀ b ∈ Set.Ioo beta 2, Antitone (rightSum b))

end Problem
