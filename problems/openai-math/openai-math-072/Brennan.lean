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

- problem_id: Brennan
- collection: openai-math
- question_id: openai-math:072
- source: openai-math
- source_locator: lean/ComparatorChallenges/Brennan.lean#OAI.Brennan.main_theorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Brennan's conjecture: for every conformal bijection ϕ from a simply connected plane domain onto the disk, $`|\phi'|^s`$ is area-integrable for $`4/3\lt s\lt 4`$. The sharp universal integral-means identity is $`B_{\mathcal S}(t)=|t|-1`$ for t ≤ −2. A strict bound $`B_b(-1)\lt 1/4`$ for bounded univalent functions disproves Kraetzer's prediction at that parameter. ([Lean](lean/docs/072.md)) We prove Brennan's conjecture: if a simply connected plane domain admits a conformal bijection φ onto the unit disk, then $`|\varphi'|^s`$ is area-integrable for every $`4/3\lt s\lt 4`$. We also prove the sharp inverse-square integral-means exponent $`B_{\mathcal S}(-2)=1`$ for the normalized schlicht class $`\mathcal S`$. We prove a uniform upper bound for inverse-first-power integral means of normalized univalent disk maps with exponent strictly below 1/4. Consequently, the bounded universal integral-means spectrum satisfies $`B_b(-1)\lt 1/4`$, disproving Kraetzer's conjectured spectrum at p = −1.
- notes: OpenAI math result family 072, Brennan's conjecture and the integral-means spectrum -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/072.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Brennan.main_theorem
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.IntegralMeans.Main
- source_main_result: OAI.Brennan.main_theorem
- source_papers: preprints/Brennans-conjecture-and-sharp-inverse-square-integral-means-September-24-2026/paper.pdf preprints/A-strict-inverse-first-power-bound-for-univalent-functions-September-24-2026/paper.pdf
- source_scope_note: lean/docs/072.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Brennan

def disk : Set ℂ := Metric.ball 0 1

def UnivalentOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ f U ∧ Set.InjOn f U

def Schlicht (f : ℂ → ℂ) : Prop :=
  UnivalentOn f disk ∧ f 0 = 0 ∧ deriv f 0 = 1

def integralMean (f : ℂ → ℂ) (t r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi,
    ‖deriv f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ t

def beta (f : ℂ → ℂ) (t : ℝ) : EReal :=
  Filter.limsup (fun r : ℝ =>
    ((Real.log (integralMean f t r) / Real.log (1 / (1 - r)) : ℝ) : EReal))
    (𝓝[<] (1 : ℝ))

def spectrum (t : ℝ) : EReal :=
  sSup {b | ∃ f : ℂ → ℂ, Schlicht f ∧ beta f t = b}

def SphericalBoundaryNontrivial (W : Set ℂ) : Prop :=
  Set.Nontrivial (frontier (((↑) : ℂ → OnePoint ℂ) '' W))

def MainStatement : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ f : ℂ → ℂ, Schlicht f →
    ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
      integralMean f (-2) r ≤ C * (1 - r) ^ (-1 - ε)) ∧
  spectrum (-2) = 1 ∧
  (∀ W : Set ℂ, IsOpen W → IsConnected W → SimplyConnectedSpace W →
    SphericalBoundaryNontrivial W → ∀ φ : ℂ → ℂ,
      DifferentiableOn ℂ φ W → Set.BijOn φ W disk →
      ∀ s : ℝ, 4 / 3 < s → s < 4 →
        IntegrableOn (fun z => ‖deriv φ z‖ ^ s) W volume) ∧
  (∀ f : ℂ → ℂ, UnivalentOn f disk → ∀ t : ℝ,
    -2 < t → t < 2 / 3 →
      IntegrableOn (fun z => ‖deriv f z‖ ^ t) disk volume)

def main_theorem_statement : Prop :=
  MainStatement

end Brennan
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Brennan.main_theorem_statement

end Problem

/- Formalization scope, from lean/docs/072.md: Brennan's conjecture asserts that $|\phi'|^s$ is area-integrable for $4/3<s<4$ when $\phi$ conformally maps a simply connected plane domain with nontrivial spherical boundary onto the disk. The formalization establishes this interval, along with area integrability of $|f'|^t$ for univalent disk maps when $-2<t<2/3$. It also gives the uniform inverse-square radial-mean bound with exponent $-1-\varepsilon$ for every $\varepsilon>0$ and the spectrum value $B_{\mathcal S}(-2)=1$. The Koebe map and its inverse give divergence at all four boundary exponents. Kraetzer's proposed integral-means spectrum predicts $B_b(-1)=1/4$ for bounded univalent maps. The formalized result proves $B_b(-1)<1/4$, contradicting that prediction. The underlying estimate gives constants $0<\varepsilon<1/4$ and $C<\infty$ such that the normalized circular mean of $|f'|^{-1}$ is at most $C(1-r)^{-1/4+\varepsilon}$ for every normalized univalent disk map and $1/2\le r<1$. The bound requires neither bounded image nor boundary regularity, and no numerical value of $\varepsilon$ is specified. -/
