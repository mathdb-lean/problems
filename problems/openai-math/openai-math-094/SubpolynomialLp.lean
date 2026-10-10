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

- problem_id: SubpolynomialLp
- collection: openai-math
- question_id: openai-math:094
- source: openai-math
- source_locator: lean/ComparatorChallenges/SubpolynomialLp.lean#OAI.SubpolynomialLp.source_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For every fixed $`1\lt p\lt \infty`$ and distortion D &gt; 1, every n-point subset of real Lp embeds into $`\ell_p^d`$ with distortion at most D and dimension $`d=n^{o(1)}`$, answering Naor's sublinear-dimension question for p ≠ 2. In contrast, exact embeddings require worst-case dimension $`\Theta(n^2)`$ when p ≠ 2. ([Lean](lean/docs/094.md)) For every fixed $`1\lt p\lt \infty`$ and D &gt; 1, every n-point subset of a real Lp space embeds into $`\ell_p^d`$ with distortion at most D and subpolynomial dimension $`d=n^{o(1)}`$. The target has the same exponent p, and the embedding need not be linear.
- notes: OpenAI math result family 094, Subpolynomial dimension reduction in <i>L</i><sub><i>p</i></sub> -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/094.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SubpolynomialLp.source_main
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.LpDimension.Main
- source_main_result: OAI.SubpolynomialLp.source_main
- source_papers: preprints/Subpolynomial-dimension-reduction-in-Lp-September-23-2026/paper.pdf
- source_scope_note: lean/docs/094.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
universe u

namespace SubpolynomialLp

def coordinateDistance (p : ℝ) {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  (∑ a, |x a - y a| ^ p) ^ (1 / p)

/-- The universal property used in the definition of d_p(n,D). -/
def GoodDimension (p : ℝ) (n : ℕ) (D : ℝ) (d : ℕ) : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
    (x : Fin n → @Lp Ω ℝ mΩ _ (ENNReal.ofReal p) μ),
    Function.Injective x →
    ∃ (y : Fin n → Fin d → ℝ) (s : ℝ), 0 < s ∧
      ∀ i j, s * ‖x i - x j‖ ≤ coordinateDistance p (y i) (y j) ∧
        coordinateDistance p (y i) (y j) ≤ D * s * ‖x i - x j‖

/-- The least universal coordinate dimension. The theorem also asserts that
this least dimension has the defining property, ruling out an empty infimum. -/
def dimension (p : ℝ) (n : ℕ) (D : ℝ) : ℕ :=
  sInf {d : ℕ | GoodDimension.{u} p n D d}

def gamma (p : ℝ) : ℝ := if p < 2 then 2 - p else 1 - 2 / p

/-- The universal coordinate dimension bounds and their logarithmic limits. -/
def source_main_statement : Prop :=
  ∀ (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2),
    (∀ D : ℝ, 1 < D → ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      GoodDimension.{u} p n D (dimension.{u} p n D) ∧
      Real.log (n : ℝ) / Real.log (1 + 2 * D) ≤ (dimension.{u} p n D : ℝ) ∧
      (dimension.{u} p n D : ℝ) ≤ Real.exp (C * Real.log (n : ℝ) ^ gamma p)) ∧
    (∀ n : ℕ, 9 ≤ n →
      GoodDimension.{u} p n 1 (dimension.{u} p n 1) ∧
      ((n - 1) / 4) ^ 2 ≤ dimension.{u} p n 1 ∧
      dimension.{u} p n 1 ≤ n.choose 2) ∧
    (∀ D : ℝ, 1 ≤ D →
      Tendsto (fun n : ℕ => Real.log (dimension.{u} p n D : ℝ) / Real.log (n : ℝ))
        atTop (𝓝 (if 1 < D then 0 else 2)))

end SubpolynomialLp

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.SubpolynomialLp.source_main_statement.{u}

end Problem

/- Formalization scope, from lean/docs/094.md: For $p>1$, $p\ne2$, the formalization bounds the least dimension needed to embed every $n$-point subset of real $L_p$ with distortion $D$. For each fixed $D>1$, there is a constant $C=C(p,D)$ such that this dimension lies between $\log n/\log(1+2D)$ and $\exp(C(\log n)^{\gamma(p)})$ for every $n\ge2$, where $\gamma(p)=2-p$ for $p<2$ and $1-2/p$ for $p>2$. At distortion $1$ and $n\ge9$, it lies between $\lfloor(n-1)/4\rfloor^2$ and $\binom n2$. The least dimension is attained, and its logarithm divided by $\log n$ tends to $0$ for $D>1$ and to $2$ for $D=1$. -/
