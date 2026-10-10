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

- problem_id: CoulombRadii
- collection: openai-math
- question_id: openai-math:263
- source: openai-math
- source_locator: lean/ComparatorChallenges/CoulombRadii.lean#OAI.NeutralAtom.generalized_outer_radii
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For the full nonrelativistic Coulomb model with two electron spin states, proves that a molecule with M fixed nuclei of charges at least one and total charge Z strictly binds at most $`Z+CM`$ electrons. Neutral-atom first ionization energies and radii containing all but an expected half-electron have universal positive upper and lower bounds. The energy cost of removing m electrons has Thomas–Fermi asymptotics as $`m\to\infty`$ and $`Z/m\to\infty`$; neutral-atom outer radii have the corresponding iterated-limit asymptotics, taking $`Z\to\infty`$ first. ([Lean](lean/docs/263.md)) We prove the energy part of the generalized ionization conjecture for full nonrelativistic Coulomb atoms with two electron spin states. The energy needed to remove m electrons is asymptotic to $`a_{\mathrm{TF}}m^{7/3}`$ whenever $`m\to\infty`$ and $`Z/m\to\infty`$, with the Thomas–Fermi constant in atomic units. We also obtain both conjectured iterated limits. We prove the radius part of the generalized ionization conjecture for neutral nonrelativistic Coulomb atoms with two spin states. For every choice of ground states, the upper and lower large-nuclear-charge limits of the radius defined by an expected exterior electron mass m are both asymptotic to $`(81\pi^2/2)^{1/3}m^{-1/3}`$ as m tends to infinity.
- notes: OpenAI math result family 263, The ionization and generalized ionization conjectures -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/263.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.NeutralAtom.generalized_outer_radii
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.CoulombRadii.Main
- source_papers: preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf
- source_scope_note: lean/docs/263.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace NeutralAtom

abbrev Position := EuclideanSpace ℝ (Fin 3)
abbrev Configuration (n : ℕ) := Fin n → Position
abbrev Spins (n : ℕ) := Fin n → Fin 2
abbrev Wavefunction (n : ℕ) := Spins n → Configuration n → ℂ
abbrev Gradient (n : ℕ) := Spins n → Fin n → Fin 3 → Configuration n → ℂ

def coordinateDirection {n : ℕ} (i : Fin n) (a : Fin 3) : Configuration n :=
  Pi.single i (EuclideanSpace.single a 1)

def HasWeakGradient {n : ℕ} (ψ : Wavefunction n) (g : Gradient n) : Prop :=
  ∀ σ i a (φ : Configuration n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, (fderiv ℝ φ x (coordinateDirection i a) : ℂ) * ψ σ x) =
      -(∫ x, (φ x : ℂ) * g σ i a x)

def IsAntisymmetric {n : ℕ} (ψ : Wavefunction n) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)) (σ : Spins n),
    (fun x : Configuration n => ψ (σ ∘ p) (x ∘ p)) =ᵐ[volume]
      (fun x => (((Equiv.Perm.sign p : ℤ) : ℂ)) * ψ σ x)

def FormDomain {n : ℕ} (ψ : Wavefunction n) (g : Gradient n) : Prop :=
  IsAntisymmetric ψ ∧ HasWeakGradient ψ g ∧
  (∀ σ, MemLp (ψ σ) 2 volume) ∧
  (∀ σ i a, MemLp (g σ i a) 2 volume) ∧
  (∀ σ i, Integrable (fun x : Configuration n => ‖x i‖⁻¹ * ‖ψ σ x‖ ^ 2)) ∧
  (∀ σ i j, i < j →
    Integrable (fun x : Configuration n => ‖x i - x j‖⁻¹ * ‖ψ σ x‖ ^ 2))

def normSquared {n : ℕ} (ψ : Wavefunction n) : ℝ :=
  ∑ σ : Spins n, ∫ x : Configuration n, ‖ψ σ x‖ ^ 2

def coulombPotential {n : ℕ} (Z : ℕ) (x : Configuration n) : ℝ :=
  -(Z : ℝ) * (∑ i : Fin n, ‖x i‖⁻¹) +
    ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), ‖x i - x j‖⁻¹

def energy {n : ℕ} (Z : ℕ) (ψ : Wavefunction n) (g : Gradient n) : ℝ :=
  (1 / 2 : ℝ) * (∑ σ : Spins n, ∑ i : Fin n, ∑ a : Fin 3,
    ∫ x : Configuration n, ‖g σ i a x‖ ^ 2) +
  ∑ σ : Spins n, ∫ x : Configuration n, coulombPotential Z x * ‖ψ σ x‖ ^ 2

def IsNormalizedGroundState (Z : ℕ) (ψ : Wavefunction Z) : Prop :=
  ∃ g : Gradient Z, FormDomain ψ g ∧ normSquared ψ = 1 ∧
    ∀ (χ : Wavefunction Z) (h : Gradient Z),
      FormDomain χ h → normSquared χ = 1 → energy Z ψ g ≤ energy Z χ h

def density {N : ℕ} (ψ : Wavefunction (N + 1)) (x : Position) : ℝ :=
  (N + 1 : ℝ) * ∑ σ : Spins (N + 1),
    ∫ y : Configuration N, ‖ψ σ (Fin.cons x y)‖ ^ 2

def exteriorMass {N : ℕ} (ψ : Wavefunction (N + 1)) (r : ℝ) : ℝ :=
  ∫ x in {x : Position | r < ‖x‖}, density ψ x

def radius {N : ℕ} (ψ : Wavefunction (N + 1)) (m : ℕ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ exteriorMass ψ r ≤ (m : ℝ)}

def bTF : ℝ := (81 * Real.pi ^ 2 / 2) ^ (1 / 3 : ℝ)

def largeCharge (m : ℕ) : Filter ℕ :=
  atTop ⊓ Filter.principal {N : ℕ | m < N + 1}

def upperRadius (Ψ : ∀ N : ℕ, Wavefunction (N + 1)) (m : ℕ) : EReal :=
  Filter.limsup (fun N : ℕ => (radius (Ψ N) m : EReal)) (largeCharge m)

def lowerRadius (Ψ : ∀ N : ℕ, Wavefunction (N + 1)) (m : ℕ) : EReal :=
  Filter.liminf (fun N : ℕ => (radius (Ψ N) m : EReal)) (largeCharge m)

def generalized_outer_radii_statement : Prop :=
  ∀ (Ψ : ∀ N : ℕ, Wavefunction (N + 1)) (hΨ : ∀ N : ℕ, IsNormalizedGroundState (N + 1) (Ψ N)),
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * upperRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) ∧
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * lowerRadius Ψ m)
      atTop (𝓝 (bTF : EReal))

end NeutralAtom
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.NeutralAtom.generalized_outer_radii_statement

end Problem

/- Formalization scope, from lean/docs/263.md: The formalization gives the large-ionization asymptotics for the full nonrelativistic two-spin Coulomb atom. Let $I_m(Z)$ be the energy needed to remove $m$ electrons from a neutral atom of nuclear charge $Z$. There is a positive coefficient $a_{\mathrm{TF}}$ with the Thomas–Fermi variational characterization such that $I_m(Z)/m^{7/3}\to a_{\mathrm{TF}}$ whenever $m\to\infty$ and $Z/m\to\infty$, with integers $Z>m\ge1$. The corresponding iterated limsup and liminf limits hold with $Z\to\infty$ first. The energy uses the full antisymmetric Sobolev form domain; fixed-$m$ convergence and ground-state attainment are outside this statement. For neutral Coulomb atoms with two electron spin states, the formalization proves the asymptotic law for generalized outer-electron radii defined by an expected exterior electron mass $m$. For every choice of normalized ground states, both the upper and lower large-nuclear-charge radius limits satisfy $m^{1/3}R_m\longrightarrow (81\pi^2/2)^{1/3}$ as $m\to\infty$. The large-nuclear-charge limit is taken first. Ground states are inputs to the statement; their existence is not asserted separately. -/
