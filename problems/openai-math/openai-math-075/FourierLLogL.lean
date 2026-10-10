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

- problem_id: FourierLLogL
- collection: openai-math
- question_id: openai-math:075
- source: openai-math
- source_locator: lean/ComparatorChallenges/FourierLLogL.lean#OAI.FourierLLogL.paperMain
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that the ordinary symmetric Fourier partial sums of every complex-valued function in $`L\log L(\mathbb T)`$ converge almost everywhere along the full sequence. This resolves the classical sufficiency conjecture at the $`L\log L`$ scale. ([Lean](lean/docs/075.md)) We prove that the ordinary symmetric Fourier partial sums of every complex-valued function in $`L\log L`$ on the circle converge almost everywhere to the function along the full sequence. This establishes the classical $`L\log L`$ sufficiency conjecture.
- notes: OpenAI math result family 075, The $`L\log L`$ Fourier-convergence conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/075.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.FourierLLogL.paperMain
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.FourierLLogL.PaperMain
- source_main_result: OAI.FourierLLogL.paperMain
- source_papers: preprints/Almost-everywhere-Fourier-convergence-in-L-log-L-September-23-2026/paper.pdf
- source_scope_note: lean/docs/075.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


open MeasureTheory Filter
open scoped BigOperators Topology

namespace OAI.FourierLLogL

instance circlePeriod_pos : Fact (0 < 2 * Real.pi) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- Almost-everywhere convergence of all symmetric Fourier partial sums in L log L. -/
def paperMain_statement : Prop :=
  ∀ (f : AddCircle (2 * Real.pi) → ℂ) (hfm : AEStronglyMeasurable f AddCircle.haarAddCircle) (hfi : Integrable (fun x ↦ ‖f x‖ * Real.log (2 + ‖f x‖))
      AddCircle.haarAddCircle),
    ∃ E : Set (AddCircle (2 * Real.pi)),
      MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧ ∀ x ∉ E,
        Tendsto
          (fun N : ℕ ↦
            ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f k * fourier k x)
          atTop (𝓝 (f x))

end OAI.FourierLLogL

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.FourierLLogL.paperMain_statement

end Problem

/- Formalization scope, from lean/docs/075.md: The $L\log L$ Fourier-convergence conjecture asks whether ordinary symmetric Fourier partial sums converge almost everywhere at this integrability scale. The formalization proves this for every measurable complex-valued function on $\mathbb T=\mathbb R/(2\pi\mathbb Z)$ satisfying $\int_{\mathbb T}|f|\log(2+|f|)<\infty$. Outside one measurable null set, $\sum_{k=-N}^{N}\widehat f(k)e^{ikx}\to f(x)$ along the full sequence $N\to\infty$. -/
