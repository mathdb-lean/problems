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

- problem_id: PlanarAndersonSpectrum
- collection: openai-math
- question_id: openai-math:261
- source: openai-math
- source_locator: lean/ComparatorChallenges/PlanarAndersonSpectrum.lean#OAI.PlanarAnderson.anderson_spectrum_ae
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the predicted spectral contrast for the lattice Anderson model with independent uniform site potentials. In dimension two, every positive disorder strength gives almost surely pure-point spectrum. In every fixed dimension d ≥ 3, sufficiently weak positive disorder gives purely absolutely continuous spectrum on a fixed open interval with nonzero spectral weight. ([Lean](lean/docs/261.md)) For each fixed positive disorder strength, we prove that the nearest-neighbor Anderson operator on the square lattice with independent uniform site potentials almost surely has pure-point spectral type throughout its spectrum. This resolves the pure-point assertion of the two-dimensional Anderson localization conjecture for the uniform single-site law.
- notes: OpenAI math result family 261, Localization and delocalization in the Anderson model -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/261.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.PlanarAnderson.anderson_spectrum_ae
- source_theorem_count: 1
- source_solution_module: OAI.MathematicalPhysics.PlanarAnderson.Spectrum
- source_papers: preprints/Pure-Point-Spectrum-for-the-Two-Dimensional-Anderson-Model-at-Every-Positive-Disorder-September-23-2026/paper.pdf
- source_scope_note: lean/docs/261.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PlanarAnderson

abbrev Site := ℤ × ℤ
abbrev Configuration := Site → ℝ
abbrev Hilbert := lp (fun _ : Site => ℂ) 2

def disorderLaw (h : ℝ) : Measure Configuration :=
  Measure.infinitePi (fun _ : Site => ProbabilityTheory.cond volume (Set.Icc (-h) h))

def IsAndersonOperator (v : Configuration) (H : Hilbert →L[ℂ] Hilbert) : Prop :=
  ∀ (u : Hilbert) (x : Site),
    (H u) x = u (x.1 + 1, x.2) + u (x.1 - 1, x.2) +
      u (x.1, x.2 + 1) + u (x.1, x.2 - 1) + (v x : ℂ) * u x

def spectralInterval (h : ℝ) : Set ℂ :=
  {z | z.im = 0 ∧ -4 - h ≤ z.re ∧ z.re ≤ 4 + h}

def anderson_spectrum_ae_statement : Prop :=
  ∀ {h : ℝ} (hh : 0 < h),
    ∀ᵐ v ∂disorderLaw h, ∃ H : Hilbert →L[ℂ] Hilbert,
      IsAndersonOperator v H ∧ IsSelfAdjoint H ∧ spectrum ℂ H = spectralInterval h

end PlanarAnderson

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.PlanarAnderson.anderson_spectrum_ae_statement

end Problem

/- Formalization scope, from lean/docs/261.md: The linked formalization proves a supporting spectral statement for the nearest-neighbor Anderson operator on $\mathbb Z^2$. For every disorder strength $h>0$ with independent site potentials uniform on $[-h,h]$, it constructs the bounded self-adjoint operator almost surely and identifies its spectrum as the real interval $[-4-h,4+h]$. This selected statement identifies the spectral set. It does not assert the pure-point spectral type claimed in the accompanying paper. -/
