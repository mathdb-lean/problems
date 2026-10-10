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

- problem_id: OrdinaryElliott
- collection: openai-math
- question_id: openai-math:007
- source: openai-math
- source_locator: lean/ComparatorChallenges/OrdinaryElliott.lean#OAI.OrdinaryCorrelations.binary_corrected_elliott
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the ordinary two-point Chowla conjecture, with a bound $`O(X/(\log X)^c)`$ for Liouville correlation sums along fixed nonproportional affine forms, where c &gt; 0 is absolute. More generally, proves the binary corrected Elliott conjecture for complex multiplicative functions bounded by one when one factor is uniformly nonpretentious against each fixed Dirichlet character times $`n^{it}`$ for $`|t|\le X`$. ([Lean](lean/docs/007.md)) We prove the ordinary two-point Chowla conjecture. For every fixed pair of nonproportional affine forms, the Liouville correlation has a power-of-logarithm saving at every cutoff, with an absolute exponent. We also prove the binary corrected Elliott conjecture for ordinary averages of complex multiplicative functions of modulus at most one, under uniform nonpretentiousness of at least one original factor. This qualitative conclusion holds in fixed residue classes and for fixed nonproportional affine forms.
- notes: OpenAI math result family 007, Ordinary two-point correlations and the corrected Elliott conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/007.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.OrdinaryCorrelations.binary_corrected_elliott
- source_theorem_count: 1
- source_solution_module: OAI.NumberTheory.OrdinaryCorrelations.Elliott.Main
- source_papers: preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf
- source_scope_note: lean/docs/007.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open scoped BigOperators
open Filter

namespace OrdinaryCorrelations

def OneBounded (f : ℕ → ℂ) : Prop := ∀ n, ‖f n‖ ≤ 1

def Multiplicative (f : ℕ → ℂ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → f (m * n) = f m * f n

def distanceSq (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t X : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 ⌊X⌋₊).filter Nat.Prime,
    (1 - (f p * star (χ (p : ZMod q) *
      Complex.exp ((t * Real.log (p : ℝ) : ℝ) * Complex.I))).re) / (p : ℝ)

def distance (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t X : ℝ) : ℝ := Real.sqrt (distanceSq f χ t X)

def UniformlyNonpretentious (f : ℕ → ℂ) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ χ : DirichletCharacter ℂ q,
    Tendsto (fun N : ℕ => sInf ((fun t : ℝ => distance f χ t (N : ℝ)) ''
      Set.Icc (-(N : ℝ)) (N : ℝ))) atTop atTop

def shiftAverage (f₁ f₂ : ℕ → ℂ) (h₁ h₂ N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f₁ (n + h₁) * f₂ (n + h₂)

def binary_corrected_elliott_statement : Prop :=
  ∀ (f₁ f₂ : ℕ → ℂ) (hf₁ : OneBounded f₁) (hf₂ : OneBounded f₂) (hm₁ : Multiplicative f₁) (hm₂ : Multiplicative f₂) (hNP : UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) (h₁ h₂ : ℕ) (hne : h₁ ≠ h₂),
    Tendsto (shiftAverage f₁ f₂ h₁ h₂) atTop (nhds 0)

end OrdinaryCorrelations
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.OrdinaryCorrelations.binary_corrected_elliott_statement

end Problem

/- Formalization scope, from lean/docs/007.md: The formalization proves ordinary two-point cancellation for multiplicative functions. For the Liouville function on every fixed pair of nonproportional affine forms, the correlation sum up to $X$ is $O(X/(\log X)^c)$ for an absolute $c>0$, with the implied constant depending on the forms. For two one-bounded multiplicative functions, if at least one is uniformly nonpretentious against all Dirichlet-character twists with frequency $|t|\le N$, then their shifted and nonproportional affine correlation sums divided by $N$ tend to zero. These are ordinary averages, with no logarithmic averaging. -/
