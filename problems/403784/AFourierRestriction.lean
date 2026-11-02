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

import FormalConjecturesUtil

/-!
Stated in this library, not converted from another corpus: `source` is this
repository, `source_locator` this file, and `source_version` the commit that
holds it.

- problem_id: AFourierRestriction
- collection: authored
- question_id: authored:FourierRestriction
- source: mathdb-lean
- source_locator: authored/FourierRestriction.lean#Target
- prose: The restriction conjecture of Stein for the sphere. In dimension n ≥ 2 the Fourier transform restricts boundedly from L^p(ℝ^n) to L^q of the unit sphere with surface measure whenever 1 ≤ p < 2n/(n+1) and q ≤ ((n-1)/(n+1)) p', with p' the conjugate exponent. Both conditions are known to be necessary; the conjecture is that they suffice. Proved for n = 2, open for every n ≥ 3.
- notes: Restriction conjecture -- https://en.wikipedia.org/wiki/Restriction_problem
- track: open
- answer_shape: proof
- source_category: research open
- source_ams: 42
- generator: adapters/authored/adapter.py
-/

open MeasureTheory Metric
open scoped FourierTransform SchwartzMap ENNReal

namespace Problem

/-- Surface measure on the unit sphere of `ℝⁿ`, as Mathlib derives it from Lebesgue measure:
`σ(s) = n · vol({r x : x ∈ s, 0 < r < 1})`. For `n ≥ 1` this is the usual `(n-1)`-dimensional
surface measure. -/
noncomputable def sphereMeasure (n : ℕ) :
    Measure (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere

/-- The restriction estimate `R(p → q)` in dimension `n`: a finite constant `C` with
`‖(𝓕 f)|_{S^{n-1}}‖_{L^q(σ)} ≤ C ‖f‖_{L^p(ℝⁿ)}` for every Schwartz function `f`. -/
def RestrictionEstimate (n : ℕ) (p q : ℝ≥0∞) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
    eLpNorm (fun ξ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        𝓕 (⇑f) (ξ : EuclideanSpace ℝ (Fin n))) q (sphereMeasure n)
      ≤ C * eLpNorm (⇑f) p volume

/-- The restriction conjecture: in dimension `n ≥ 2`, `R(p → q)` holds whenever
`1 ≤ p < 2n/(n+1)` and `q ≤ ((n-1)/(n+1)) p'` where `p' = p/(p-1)`. The second condition is
written without division as `(n+1) q (p-1) ≤ (n-1) p`, which for `p = 1` is no condition at
all, matching `p' = ∞`. -/
abbrev Target : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p q : ℝ, 1 ≤ p → p < 2 * n / (n + 1) → 1 ≤ q →
    (n + 1) * q * (p - 1) ≤ (n - 1) * p →
    RestrictionEstimate n (ENNReal.ofReal p) (ENNReal.ofReal q)

end Problem

/-!
- source_version: 2fe7c76111373ea1d5503c074350e836cf33de46
-/
