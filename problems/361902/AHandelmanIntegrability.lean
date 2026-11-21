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

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Handelman’s integrability conjecture for log-convex functions (MathDB 361902).
Authored directly from the mathematical source.

- problem_id: AHandelmanIntegrability
- collection: authored
- question_id: authored:HandelmanIntegrability
- source: mathdb-lean
- source_locator: problems/361902/AHandelmanIntegrability.lean#Problem.Target
- prose: A positive log-convex function h on (0,infinity) is integrable there if h(n)/h(n+1) tends to one and h(x)^2/h(2x) is integrable there.
- notes: https://mathdb.com/p/361902/handelman-s-integrability-conjecture-for-log-convex-function
- track: solved
- answer_shape: proof

Reference: Brian Simanek, On Some Convexity Questions of Handelman, arXiv:2402.10970v1, Conjecture 1 and Theorem 2. https://arxiv.org/pdf/2402.10970v1

Positivity and log-convexity are imposed only on the positive half-line. Values of the total Lean function outside that domain are irrelevant. The natural-number ratio sequence starts at n+1, avoiding the excluded endpoint zero; a finite index shift does not change the limit. IntegrableOn is Lebesgue integrability. The primary paper proves this conjecture as Theorem 2; its negative result concerns a different, converse question.
-/

open MeasureTheory Filter

namespace Problem

/-- Handelman’s conjecture, proved in the source as Theorem 2. -/
abbrev Target : Prop :=
  ∀ h : ℝ → ℝ, (∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) →
    ConvexOn ℝ (Set.Ioi 0) (fun x => Real.log (h x)) →
    Tendsto (fun n : ℕ => h ((n : ℝ) + 1) / h ((n : ℝ) + 2)) atTop (nhds 1) →
    IntegrableOn (fun x => h x ^ 2 / h (2 * x)) (Set.Ioi 0) volume →
      IntegrableOn h (Set.Ioi 0) volume

end Problem
