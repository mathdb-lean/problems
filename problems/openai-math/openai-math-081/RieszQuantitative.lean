import Mathlib
/-
Copyright 2026 OpenAI. Licensed under the Apache License, Version 2.0.
Copyright 2026 The mathdb-lean Authors.

The definitions and the statements below are OpenAI's, from
github.com/openai/math at the revision named in the metadata block; see NOTICE.
What this library changed: each `sorry`-bodied theorem became the definition of
the proposition it stated, and `Problem.Target` conjoins those propositions.

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

/-!
Converted from github.com/openai/math. `source_locator` names the comparator
challenge this came from and `source_solution_module` the module there that
proves it; both are at `source_version`. The definitions are the challenge's
own; each sorried theorem became `<name>_statement`, and `Problem.Target`
below conjoins them. `track` is solved because comparator accepted OpenAI's
proof against this very statement. Whether the statement says what the paper's
title says is what the scope note, carried as a caveat, is about.

- problem_id: RieszQuantitative
- collection: openai-math
- question_id: openai-math:081
- source: openai-math
- source_locator: lean/ComparatorChallenges/RieszQuantitative.lean#OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the remaining higher-codimension Riesz-transform rectifiability problem: for d ≥ 4 and $`2\le n\le d-2`$, an n-Ahlfors–David regular Radon measure on ℝd is uniformly n-rectifiable whenever its n-dimensional Riesz transform is uniformly L2-bounded over all positive hard truncations. The rectifiability bounds depend only on dimension, regularity and operator bounds. ([Lean](lean/docs/081.md)) We prove that an n-Ahlfors–David regular Radon measure on ℝd is uniformly n-rectifiable if its n-dimensional Riesz transform is uniformly bounded from scalar $`L^2(\mu)`$ to vector-valued $`L^2(\mu)`$ over all positive hard truncations, for integers d ≥ 4 and $`2\le n\le d-2`$. This gives a positive answer to the David–Semmes Riesz-transform question in its remaining higher-codimension range. The conclusion gives uniform big pieces of Lipschitz images of Euclidean balls.
- notes: OpenAI math result family 081, Riesz transforms and rectifiability in higher codimension -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/081.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.RieszRectifiability.Main
- source_main_result: OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability
- source_papers: preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf
- source_scope_note: lean/docs/081.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace RieszRectifiability
noncomputable section
open MeasureTheory Set Metric
open scoped NNReal ENNReal

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

def AdmissibleRadius {d : ℕ} (μ : Measure (Ambient d)) (r : ℝ) : Prop :=
  0 < r ∧ ENNReal.ofReal r ≤ Metric.ediam μ.support

def kernel {d : ℕ} (n : ℕ) (x y : Ambient d) : Ambient d :=
  (‖x - y‖ ^ (n + 1))⁻¹ • (x - y)

def truncated {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (ε : ℝ) (f : Ambient d → ℝ) (x : Ambient d) : Ambient d :=
  ∫ y in {y | ε < dist x y}, f y • kernel n x y ∂μ

def ADRegularWithConstant {d : ℕ} (n : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) : Prop :=
  1 ≤ C ∧ ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
    ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r) ∧
    μ (ball x r) ≤ ENNReal.ofReal (C * r ^ n)

def RieszL2BoundedWithConstant {d : ℕ} (n : ℕ) (C : ℝ≥0)
    (μ : Measure (Ambient d)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ,
    MemLp f 2 μ → MemLp (truncated n μ ε f) 2 μ ∧
      eLpNorm (truncated n μ ε f) 2 μ ≤ (C : ℝ≥0∞) * eLpNorm f 2 μ

def BallImageConclusion {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (θ : ℝ) (M : ℝ≥0) : Prop :=
  ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
    ∃ g : (ball (0 : Ambient n) r) → Ambient d,
      LipschitzWith M g ∧
      ENNReal.ofReal (θ * r ^ n) ≤ μ (ball x r ∩ range g)

/-- A single mass fraction and Lipschitz bound work for all measures with fixed AD and Riesz bounds. -/
def QuantitativeFullStatement : Prop :=
  ∀ d n : ℕ, 4 ≤ d → 2 ≤ n → n + 2 ≤ d →
    ∀ C_AD : ℝ, 1 ≤ C_AD → ∀ C_R : ℝ≥0,
      ∃ θ : ℝ, 0 < θ ∧ ∃ M : ℝ≥0,
        ∀ μ : Measure (Ambient d), μ.Regular →
          ADRegularWithConstant n C_AD μ →
          RieszL2BoundedWithConstant n C_R μ →
          BallImageConclusion n μ θ M

end
end RieszRectifiability

namespace RieszRectifiability

/-- Class-uniform Lipschitz ball images from fixed AD and hard-truncation L² bounds. -/
def quantitative_higher_codimension_riesz_rectifiability_statement : Prop :=
  QuantitativeFullStatement

end RieszRectifiability

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability_statement

end Problem

/- Formalization scope, from lean/docs/081.md: The formalized result proves that bounded Riesz transforms force quantitative uniform rectifiability in higher codimension. For $d\ge4$ and $2\le n\le d-2$, an $n$-Ahlfors–David regular measure whose positive hard truncations have one uniform $L^2$ operator bound has big pieces of Lipschitz images. The mass fraction and Lipschitz constant depend only on the dimensions and the stated regularity and operator bounds, and work at every support point and admissible radius, including unbounded support. The variation and principal-value corollary is not included. -/
