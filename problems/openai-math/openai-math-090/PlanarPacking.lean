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

- problem_id: PlanarPacking
- collection: openai-math
- question_id: openai-math:090
- source: openai-math
- source_locator: lean/ComparatorChallenges/PlanarPacking.lean#OAI.sharp_fourier_certificate
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that the triangular lattice minimizes the lower limit of energy per particle for every nonnegative completely monotone potential of squared distance among locally finite planar configurations of centered-disk density one. It also minimizes unit-background renormalized Riesz energies for $`0\lt s\lt 2`$ and Coulomb energy, resolving Sandier–Serfaty and the two-dimensional Brauchart–Hardin–Saff conjecture on the linear term of optimal spherical logarithmic energy. ([Lean](lean/docs/090.md)) We prove that the density-one triangular lattice minimizes the lower energy per particle for every nonnegative completely monotone function of squared distance, among all locally finite planar configurations of centered disk density one. The comparison includes infinite energies. The proof constructs sharp Gaussian Fourier minorants using an atomic interpolation certificate. We resolve the planar Cohn–Elkies sharpness conjecture: the two-point Fourier bound attains the optimal circle-packing density $`\pi/(2\sqrt3)`$. We construct a radial Schwartz certificate and prove its global sign conditions using rigorous interval arithmetic and analytic estimates. The same certificate recovers the classical uniqueness of the triangular packing among periodic equality cases.
- notes: OpenAI math result family 090, Triangular-lattice optimality, long-range Riesz and Coulomb energies, and spherical logarithmic energy -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/090.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.sharp_fourier_certificate
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.PlanarPacking.Main
- source_papers: preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf
- source_scope_note: lean/docs/090.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-!
# A sharp Fourier certificate for planar circle packing

The normalization and Fourier convention are those of
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open MeasureTheory

namespace SharpPlanar

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Radiality of a real function on the Euclidean plane. -/
def Radial (f : Plane → ℝ) : Prop :=
  ∀ x y, ‖x‖ = ‖y‖ → f x = f y

/-- Fourier transformation with kernel `exp (-2πi⟪x, ξ⟫)`. -/
noncomputable def fourier (f : Plane → ℝ) (ξ : Plane) : ℂ :=
  ∫ x : Plane, (f x : ℂ) *
    Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I)

/-- A normalized sharp certificate for disks of radius one half. -/
def SharpCertificate (f : SchwartzMap Plane ℝ) : Prop :=
  Radial f ∧ fourier f 0 = 1 ∧ f 0 = 2 / Real.sqrt 3 ∧
    (∀ ξ, (fourier f ξ).im = 0 ∧ 0 ≤ (fourier f ξ).re) ∧
    (∀ x, 1 ≤ ‖x‖ → f x ≤ 0)

end SharpPlanar

/-- The sharp Fourier certificate theorem. -/
def sharp_fourier_certificate_statement : Prop :=
  ∃ f : SchwartzMap SharpPlanar.Plane ℝ, SharpPlanar.SharpCertificate f

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.sharp_fourier_certificate_statement

end Problem

/- Formalization scope, from lean/docs/090.md: The formalization proves that the density-one triangular lattice minimizes lower energy per particle among all locally finite planar configurations of centered-disk density one, for every nonnegative completely monotone function of squared distance. Infinite energies are allowed in the comparison. It also constructs sharp radial Schwartz minorants for every Gaussian potential: each minorant lies below the Gaussian, has nonnegative real Fourier transform, agrees with the Gaussian at nonzero triangular-lattice points, and vanishes on nonzero dual-lattice points after Fourier transformation. For the stated parameter range, the formalization includes the explicit atomic interpolation construction. The planar Cohn–Elkies sharpness conjecture asks whether the two-point Fourier method attains the optimal circle-packing density. The formalization constructs a radial Schwartz function $f$ on $\mathbb R^2$ with $\widehat f(0)=1$, $f(0)=2/\sqrt3$, $\widehat f$ real and nonnegative everywhere, and $f(x)\le0$ whenever $\|x\|\ge1$. These are the sharp Fourier certificate conditions yielding density $\pi/(2\sqrt3)$. The separate uniqueness statement for periodic equality cases is outside this selected theorem. -/
