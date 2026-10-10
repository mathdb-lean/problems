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

- problem_id: LiebThirring
- collection: openai-math
- question_id: openai-math:262
- source: openai-math
- source_locator: lean/ComparatorChallenges/LiebThirring.lean#OAI.SharpLiebThirring.sharp_lieb_thirring
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the sharp one-dimensional Lieb–Thirring inequality for $`1/2\lt \gamma\lt 3/2`$ and arbitrary finite-matrix potentials W ≥ 0 with $`\int\mathop{\mathrm{tr}}\nolimits (W^{\gamma+1/2})\lt \infty`$: the optimal constant is the scalar one-bound-state value, independent of matrix size. All equality cases are direct sums, in one constant unitary basis, of scalar sech2 solitons with independent scales and centers, and zero channels. ([Lean](lean/docs/262.md)) We resolve affirmatively the remaining cases of the scalar one-dimensional Lieb–Thirring conjecture: for every $`\frac12\lt \gamma\lt \frac32`$, the optimal constant is the one-bound-state constant. The estimate holds for every nonnegative potential in $`L^{\gamma+1/2}(\mathbb R)`$, with all negative eigenvalues included.
- notes: OpenAI math result family 262, Sharp finite-matrix Lieb–Thirring inequalities and all equality cases -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/262.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SharpLiebThirring.sharp_lieb_thirring
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.LiebThirring.Main
- source_main_result: OAI.SharpLiebThirring.sharp_lieb_thirring
- source_papers: preprints/Sharp-One-Dimensional-Lieb-Thirring-Constants-September-23-2026/paper.pdf
- source_scope_note: lean/docs/262.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI


/-!
The form domain is H¹(R;C), represented by an L² function together with its L²
weak derivative. Null-set changes do not affect any definition below.
`negativeMoment` is the extended nonnegative sum over negative eigenvalues,
counting multiplicities: equivalently the supremum over all finite orthonormal
families of weak eigenfunctions of the form. This does not assume in advance
finiteness of the moment or a finite number of eigenvalues.
-/


noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix

namespace SharpLiebThirring

structure H1 where
  val : ℝ → ℂ
  grad : ℝ → ℂ
  val_memLp : MemLp val 2 volume
  grad_memLp : MemLp grad 2 volume
  weak_derivative : ∀ φ : ℝ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    (∫ x : ℝ, val x * deriv φ x) = -(∫ x : ℝ, grad x * φ x)

def l2Pairing (u v : H1) : ℂ := ∫ x : ℝ, star (u.val x) * v.val x

/-- The polarized form of -d²/dx² - W, on exactly H¹. -/
def schrodingerForm (W : ℝ → ℝ) (u v : H1) : ℂ :=
  (∫ x : ℝ, star (u.grad x) * v.grad x) -
    ∫ x : ℝ, (W x : ℂ) * star (u.val x) * v.val x

/-- Weak eigenfunction at the negative energy -k². -/
def IsNegativeEigenfunction (W : ℝ → ℝ) (k : ℝ) (u : H1) : Prop :=
  0 < k ∧ ∀ v : H1, schrodingerForm W v u = -(k ^ 2 : ℝ) * l2Pairing v u

def IsOrthonormalFamily {N : ℕ} (u : Fin N → H1) : Prop :=
  ∀ i j, l2Pairing (u i) (u j) = if i = j then 1 else 0

/-- An unlimited finite-family-size supremum, in ℝ≥0∞, includes the entire sum. -/
def negativeMoment (γ : ℝ) (W : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ (N : ℕ) (u : Fin N → H1) (k : Fin N → ℝ)
    (_ : IsOrthonormalFamily u) (_ : ∀ i, IsNegativeEigenfunction W (k i) (u i)),
      ∑ i, (ENNReal.ofReal (k i)) ^ (2 * γ)

/-- The moment retaining at most one negative eigenvalue. -/
def oneStateMoment (γ : ℝ) (W : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ (u : H1) (k : ℝ) (_ : l2Pairing u u = 1)
    (_ : IsNegativeEigenfunction W k u), (ENNReal.ofReal k) ^ (2 * γ)

def Admissible (γ : ℝ) (W : ℝ → ℝ) : Prop :=
  (∀ᵐ x : ℝ, 0 ≤ W x) ∧ MemLp W (ENNReal.ofReal (γ + 1 / 2)) volume

def potentialMass (γ : ℝ) (W : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, (ENNReal.ofReal (W x)) ^ (γ + 1 / 2)

def semiclassicalConstant (γ : ℝ) : ℝ :=
  Real.Gamma (γ + 1) / (2 * Real.sqrt Real.pi * Real.Gamma (γ + 3 / 2))

def sharpConstant (γ : ℝ) : ℝ :=
  2 * ((γ - 1 / 2) / (γ + 1 / 2)) ^ (γ - 1 / 2) * semiclassicalConstant γ

def optimalConstant (γ : ℝ) : ℝ≥0∞ :=
  ⨆ (W : ℝ → ℝ) (_ : Admissible γ W) (_ : 0 < potentialMass γ W),
    negativeMoment γ W / potentialMass γ W

def oneStateConstant (γ : ℝ) : ℝ≥0∞ :=
  ⨆ (W : ℝ → ℝ) (_ : Admissible γ W) (_ : 0 < potentialMass γ W),
    oneStateMoment γ W / potentialMass γ W

def equalityPotential (γ : ℝ) (x : ℝ) : ℝ :=
  let r := (γ - 1 / 2)⁻¹
  (r + 1) * (Real.cosh (r * x))⁻¹ ^ 2

/-- The full spectral bound, optimal constants, and attainment at the explicit potential. -/
def MainClaim : Prop :=
  ∀ γ : ℝ, 1 / 2 < γ → γ < 3 / 2 →
    (∀ W : ℝ → ℝ, Admissible γ W →
      negativeMoment γ W ≤ ENNReal.ofReal (sharpConstant γ) * potentialMass γ W) ∧
    optimalConstant γ = ENNReal.ofReal (sharpConstant γ) ∧
    oneStateConstant γ = ENNReal.ofReal (sharpConstant γ) ∧
    Admissible γ (equalityPotential γ) ∧
    0 < potentialMass γ (equalityPotential γ) ∧
    negativeMoment γ (equalityPotential γ) =
      ENNReal.ofReal (sharpConstant γ) * potentialMass γ (equalityPotential γ)

/-- Full sharp Lieb–Thirring bound, both optimal constants, and equality at the
explicit potential; no finite spectral cutoff is imposed. -/
def sharp_lieb_thirring_statement : Prop :=
  MainClaim

end SharpLiebThirring
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SharpLiebThirring.sharp_lieb_thirring_statement

end Problem

/- Formalization scope, from lean/docs/262.md: The formalized result determines the sharp one-dimensional Lieb–Thirring constant for $1/2<\gamma<3/2$. For every nonnegative $W\in L^{\gamma+1/2}(\mathbb R)$, it bounds the full negative-eigenvalue moment of $-d^2/dx^2-W$ by the one-bound-state constant times the potential integral. This constant is optimal and is attained by $(r+1)\mathrm{sech}^2(rx)$, where $r=(\gamma-1/2)^{-1}$. No finite spectral cutoff is imposed. -/
