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

- problem_id: CoulombIonization
- collection: openai-math
- question_id: openai-math:263
- source: openai-math
- source_locator: lean/ComparatorChallenges/CoulombIonization.lean#OAI.CoulombAtom.generalized_ionization
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For the full nonrelativistic Coulomb model with two electron spin states, proves that a molecule with M fixed nuclei of charges at least one and total charge Z strictly binds at most $`Z+CM`$ electrons. Neutral-atom first ionization energies and radii containing all but an expected half-electron have universal positive upper and lower bounds. The energy cost of removing m electrons has Thomas–Fermi asymptotics as $`m\to\infty`$ and $`Z/m\to\infty`$; neutral-atom outer radii have the corresponding iterated-limit asymptotics, taking $`Z\to\infty`$ first. ([Lean](lean/docs/263.md)) We prove the energy part of the generalized ionization conjecture for full nonrelativistic Coulomb atoms with two electron spin states. The energy needed to remove m electrons is asymptotic to $`a_{\mathrm{TF}}m^{7/3}`$ whenever $`m\to\infty`$ and $`Z/m\to\infty`$, with the Thomas–Fermi constant in atomic units. We also obtain both conjectured iterated limits. We prove the radius part of the generalized ionization conjecture for neutral nonrelativistic Coulomb atoms with two spin states. For every choice of ground states, the upper and lower large-nuclear-charge limits of the radius defined by an expected exterior electron mass m are both asymptotic to $`(81\pi^2/2)^{1/3}m^{-1/3}`$ as m tends to infinity.
- notes: OpenAI math result family 263, The ionization and generalized ionization conjectures -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/263.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CoulombAtom.generalized_ionization
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.CoulombIonization.Main
- source_main_result: OAI.CoulombAtom.generalized_ionization
- source_papers: preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf
- source_scope_note: lean/docs/263.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

noncomputable section
namespace CoulombAtom

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Configuration (N : ℕ) := Fin N → Space
abbrev Spins (N : ℕ) := Fin N → Fin 2

structure FormVector (N : ℕ) where
  value : Spins N → Configuration N → ℂ
  gradient : Spins N → Fin N → Fin 3 → Configuration N → ℂ

def direction {N : ℕ} (i : Fin N) (a : Fin 3) : Configuration N :=
  Pi.single i (EuclideanSpace.single a 1)

def FormAdmissible {N : ℕ} (ψ : FormVector N) : Prop :=
  (∀ s, MemLp (ψ.value s) 2) ∧
  (∀ s i a, MemLp (ψ.gradient s i a) 2) ∧
  (∀ s i a (φ : Configuration N → ℝ),
    ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, ψ.value s x * Complex.ofReal (lineDeriv ℝ φ x (direction i a))) =
      -(∫ x, ψ.gradient s i a x * (φ x : ℂ))) ∧
  (∀ (π : Equiv.Perm (Fin N)) s, ∀ᵐ x,
    ψ.value (s ∘ π) (x ∘ π) =
      (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value s x)) ∧
  (∑ s : Spins N, ∫ x, ‖ψ.value s x‖ ^ 2) = 1 ∧
  (∀ s i, Integrable (fun x => ‖ψ.value s x‖ ^ 2 / ‖x i‖)) ∧
  (∀ s i j, i ≠ j →
    Integrable (fun x => ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖))

def formEnergy {N : ℕ} (Z : ℝ) (ψ : FormVector N) : ℝ :=
  (1 / 2 : ℝ) *
      (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        (∫ x, ‖ψ.gradient s i a x‖ ^ 2)) -
    Z * (∑ s : Spins N, ∑ i : Fin N,
      (∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
    (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
      if i < j then (∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖) else 0)

def energy (Z : ℝ) (N : ℕ) : ℝ :=
  if N = 0 then 0 else sInf {e | ∃ ψ : FormVector N,
    FormAdmissible ψ ∧ formEnergy Z ψ = e}

def ionization (m Z : ℕ) : ℝ :=
  energy Z (Z - m) - energy Z Z

def tfKinetic : ℝ := (3 / 10 : ℝ) * (3 * Real.pi ^ 2) ^ (2 / 3 : ℝ)

def directIntegrand (ρ : Space → ℝ) (p : Space × Space) : ℝ :=
  ρ p.1 * ρ p.2 / ‖p.1 - p.2‖

def TFAdmissible (M : ℝ) (ρ : Space → ℝ) : Prop :=
  (∀ᵐ x, 0 ≤ ρ x) ∧ Integrable ρ ∧ (∫ x, ρ x) = M ∧
  Integrable (fun x => ρ x ^ (5 / 3 : ℝ)) ∧
  Integrable (fun x => ρ x / ‖x‖) ∧ Integrable (directIntegrand ρ)

def tfFunctional (Z : ℝ) (ρ : Space → ℝ) : ℝ :=
  tfKinetic * (∫ x, ρ x ^ (5 / 3 : ℝ)) - Z * (∫ x, ρ x / ‖x‖) +
    (1 / 2 : ℝ) * ∫ p, directIntegrand ρ p

def tfEnergy (Z M : ℝ) : ℝ :=
  sInf {e | ∃ ρ : Space → ℝ, TFAdmissible M ρ ∧ tfFunctional Z ρ = e}

def tfIonization (m Z : ℝ) : ℝ := tfEnergy Z (Z - m) - tfEnergy Z Z

def TFCharacterization (a : ℝ) : Prop :=
  ∀ m : ℝ, 0 < m →
    Tendsto (tfIonization m) atTop (𝓝 (a * m ^ (7 / 3 : ℝ)))

def JointLimit (a : ℝ) : Prop :=
  ∀ m Z : ℕ → ℕ, (∀ j, 1 ≤ m j ∧ m j < Z j) →
    Tendsto m atTop atTop →
    Tendsto (fun j => (Z j : ℝ) / (m j : ℝ)) atTop atTop →
    Tendsto (fun j => ionization (m j) (Z j) / (m j : ℝ) ^ (7 / 3 : ℝ))
      atTop (𝓝 a)

def IteratedLimits (a : ℝ) : Prop :=
  Tendsto (fun m : ℕ => (limsup (ionization m) atTop) / (m : ℝ) ^ (7 / 3 : ℝ))
    atTop (𝓝 a) ∧
  Tendsto (fun m : ℕ => (liminf (ionization m) atTop) / (m : ℝ) ^ (7 / 3 : ℝ))
    atTop (𝓝 a)

def MainStatement : Prop :=
  ∃ a : ℝ, 0 < a ∧ TFCharacterization a ∧ JointLimit a ∧ IteratedLimits a

def generalized_ionization_statement : Prop :=
  MainStatement

end CoulombAtom

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.CoulombAtom.generalized_ionization_statement

end Problem

/- Formalization scope, from lean/docs/263.md: The formalization gives the large-ionization asymptotics for the full nonrelativistic two-spin Coulomb atom. Let $I_m(Z)$ be the energy needed to remove $m$ electrons from a neutral atom of nuclear charge $Z$. There is a positive coefficient $a_{\mathrm{TF}}$ with the Thomas–Fermi variational characterization such that $I_m(Z)/m^{7/3}\to a_{\mathrm{TF}}$ whenever $m\to\infty$ and $Z/m\to\infty$, with integers $Z>m\ge1$. The corresponding iterated limsup and liminf limits hold with $Z\to\infty$ first. The energy uses the full antisymmetric Sobolev form domain; fixed-$m$ convergence and ground-state attainment are outside this statement. For neutral Coulomb atoms with two electron spin states, the formalization proves the asymptotic law for generalized outer-electron radii defined by an expected exterior electron mass $m$. For every choice of normalized ground states, both the upper and lower large-nuclear-charge radius limits satisfy $m^{1/3}R_m\longrightarrow (81\pi^2/2)^{1/3}$ as $m\to\infty$. The large-nuclear-charge limit is taken first. Ground states are inputs to the statement; their existence is not asserted separately. -/
