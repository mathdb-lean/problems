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

- problem_id: TriangularEnergy
- collection: openai-math
- question_id: openai-math:090
- source: openai-math
- source_locator: lean/ComparatorChallenges/TriangularEnergy.lean#OAI.AtomicTriangular.universal_energy_minimum
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that the triangular lattice minimizes the lower limit of energy per particle for every nonnegative completely monotone potential of squared distance among locally finite planar configurations of centered-disk density one. It also minimizes unit-background renormalized Riesz energies for $`0\lt s\lt 2`$ and Coulomb energy, resolving Sandier–Serfaty and the two-dimensional Brauchart–Hardin–Saff conjecture on the linear term of optimal spherical logarithmic energy. ([Lean](lean/docs/090.md)) We prove that the density-one triangular lattice minimizes the lower energy per particle for every nonnegative completely monotone function of squared distance, among all locally finite planar configurations of centered disk density one. The comparison includes infinite energies. The proof constructs sharp Gaussian Fourier minorants using an atomic interpolation certificate. We resolve the planar Cohn–Elkies sharpness conjecture: the two-point Fourier bound attains the optimal circle-packing density $`\pi/(2\sqrt3)`$. We construct a radial Schwartz certificate and prove its global sign conditions using rigorous interval arithmetic and analytic estimates. The same certificate recovers the classical uniqueness of the triangular packing among periodic equality cases.
- notes: OpenAI math result family 090, Triangular-lattice optimality, long-range Riesz and Coulomb energies, and spherical logarithmic energy -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/090.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.AtomicTriangular.universal_energy_minimum
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.Triangular.Energy.Universal
- source_papers: preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf
- source_scope_note: lean/docs/090.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal
open Classical Filter

namespace TriangularUniversal

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def LocallyFinite (C : Set Plane) : Prop :=
  ∀ R : ℝ, (C ∩ Metric.closedBall (0 : Plane) R).Finite

def diskPoints (C : Set Plane) (R : ℝ) : Finset Plane :=
  if h : (C ∩ Metric.closedBall (0 : Plane) R).Finite then h.toFinset else ∅

def diskCount (C : Set Plane) (R : ℝ) : ℕ := (diskPoints C R).card

def DensityOne (C : Set Plane) : Prop :=
  Tendsto (fun R : ℝ => (diskCount C R : ℝ) / (Real.pi * R ^ 2))
    atTop (𝓝 1)

def AdmissiblePotential (g : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioi 0) ∧
  (∀ t : ℝ, 0 < t → 0 ≤ g t) ∧
  ∀ (r : ℕ) (t : ℝ), 0 < t → 0 ≤ (-1 : ℝ) ^ r * iteratedDeriv r g t

def diskEnergy (g : ℝ → ℝ) (C : Set Plane) (R : ℝ) : ℝ≥0∞ :=
  (diskCount C R : ℝ≥0∞)⁻¹ *
    ∑ x ∈ diskPoints C R, ∑ y ∈ (diskPoints C R).erase x,
      ENNReal.ofReal (g (‖x - y‖ ^ 2))

def energy (g : ℝ → ℝ) (C : Set Plane) : ℝ≥0∞ :=
  Filter.liminf (diskEnergy g C) atTop

end TriangularUniversal

namespace AtomicTriangular

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def b : ℝ := Real.sqrt 3 / 2

def triangularPoint (jk : ℤ × ℤ) : Plane :=
  (Real.sqrt b)⁻¹ •
    (EuclideanSpace.single 0 ((jk.1 : ℝ) + (jk.2 : ℝ) / 2) +
      EuclideanSpace.single 1 ((jk.2 : ℝ) * b))

def A : Set Plane := Set.range triangularPoint

abbrev LocallyFinite := TriangularUniversal.LocallyFinite
abbrev diskPoints := TriangularUniversal.diskPoints
abbrev diskCount := TriangularUniversal.diskCount
abbrev DensityOne := TriangularUniversal.DensityOne
abbrev AdmissiblePotential := TriangularUniversal.AdmissiblePotential
abbrev diskEnergy := TriangularUniversal.diskEnergy
abbrev energy := TriangularUniversal.energy

/-- The full nonzero-lattice energy, allowing a divergent series. -/
def latticeEnergy (g : ℝ → ℝ) : ℝ≥0∞ :=
  ∑' a : {x : Plane // x ∈ A ∧ x ≠ 0}, ENNReal.ofReal (g (‖a.val‖ ^ 2))

/-- Universal energy minimality for smooth completely monotone potentials, with attainment. -/
def universal_energy_minimum_statement : Prop :=
  ∀ (g : ℝ → ℝ) (C : Set Plane) (hg : AdmissiblePotential g) (hC : LocallyFinite C) (hd : DensityOne C),
    latticeEnergy g ≤ energy g C ∧ latticeEnergy g = energy g A

end AtomicTriangular
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.AtomicTriangular.universal_energy_minimum_statement

end Problem

/- Formalization scope, from lean/docs/090.md: The formalization proves that the density-one triangular lattice minimizes lower energy per particle among all locally finite planar configurations of centered-disk density one, for every nonnegative completely monotone function of squared distance. Infinite energies are allowed in the comparison. It also constructs sharp radial Schwartz minorants for every Gaussian potential: each minorant lies below the Gaussian, has nonnegative real Fourier transform, agrees with the Gaussian at nonzero triangular-lattice points, and vanishes on nonzero dual-lattice points after Fourier transformation. For the stated parameter range, the formalization includes the explicit atomic interpolation construction. The planar Cohn–Elkies sharpness conjecture asks whether the two-point Fourier method attains the optimal circle-packing density. The formalization constructs a radial Schwartz function $f$ on $\mathbb R^2$ with $\widehat f(0)=1$, $f(0)=2/\sqrt3$, $\widehat f$ real and nonnegative everywhere, and $f(x)\le0$ whenever $\|x\|\ge1$. These are the sharp Fourier certificate conditions yielding density $\pi/(2\sqrt3)$. The separate uniqueness statement for periodic equality cases is outside this selected theorem. -/
