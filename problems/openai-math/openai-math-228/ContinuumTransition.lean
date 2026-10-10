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

- problem_id: ContinuumTransition
- collection: openai-math
- question_id: openai-math:228
- source: openai-math
- source_locator: lean/ComparatorChallenges/ContinuumTransition.lean#OAI.ContinuumTemperature.main_theorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs stable distance-dependent pair interactions for three-dimensional classical particles with a first-order phase transition: the canonical free energy has a derivative jump at one inverse temperature throughout an open density interval. One potential has a divergent repulsive core; another is bounded and continuous with an integrable power-law tail, realizing the type of transition sought in Simon's continuum problem. ([Lean](lean/docs/228.md)) We construct a stable radial pair potential in three dimensions whose canonical free energy has a strict downward derivative jump at one common finite positive inverse temperature throughout an open interval of positive densities. The potential has a divergent repulsive core, a nontrivial attractive interval, and an integrable tail satisfying $`\phi(r)=o(r^{-3})`$. Its free-cube canonical free energy is finite at every positive inverse temperature and density. We construct a bounded, continuous, stable radial pair potential in three dimensions with $`|\phi(r)|\le Cr^{-3-1/32}`$ for r ≥ 1. Throughout an open interval of positive densities, its canonical thermodynamic free energy is finite at every positive inverse temperature and has a strict downward derivative jump at one common finite positive inverse temperature.
- notes: OpenAI math result family 228, Continuum phase transitions for radial pair potentials -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/228.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ContinuumTemperature.main_theorem
- source_theorem_count: 1
- source_solution_module: OAI.Probability.ContinuumTransition.Main
- source_main_result: OAI.ContinuumTemperature.main_theorem
- source_papers: preprints/A-continuum-temperature-singularity-for-a-radial-pair-potential-September-24-2026/paper.pdf preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf
- source_scope_note: lean/docs/228.md
- source_field: Probability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

abbrev Space := EuclideanSpace ℝ (Fin 3)

noncomputable def radialPotential (φ : ℝ → ℝ) (x : Space) : EReal :=
  if x = 0 then ⊤ else (φ ‖x‖ : EReal)

noncomputable def energy (φ : ℝ → ℝ) {N : ℕ} (x : Fin N → Space) : EReal :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
    radialPotential φ (x i - x j)

def Admissible (φ : ℝ → ℝ) : Prop :=
  Measurable (radialPotential φ) ∧
  (∀ a b : ℝ, 0 < a → a ≤ b →
    BddAbove (φ '' Icc a b) ∧ BddBelow (φ '' Icc a b)) ∧
  Tendsto φ (𝓝[>] (0 : ℝ)) atTop ∧
  (∃ r₁ r₂ a : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ 0 < a ∧
    ∀ r ∈ Icc r₁ r₂, φ r ≤ -a) ∧
  (∃ R : ℝ, 0 < R ∧ IntegrableOn (fun r : ℝ => r ^ 2 * |φ r|) (Ioi R)) ∧
  (∃ B : ℝ, ∀ (N : ℕ) (x : Fin N → Space),
    ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)

def cube (L : ℝ) : Set Space :=
  {x | ∀ i, x i ∈ Icc (-L / 2) (L / 2)}

noncomputable def boltzmann (φ : ℝ → ℝ) (β : ℝ) {N : ℕ}
    (x : Fin N → Space) : ℝ :=
  if energy φ x = ⊤ then 0 else Real.exp (-β * (energy φ x).toReal)

noncomputable def partition (φ : ℝ → ℝ) (β L : ℝ) (N : ℕ) : ℝ :=
  if N = 0 then 1 else
    (1 / (N.factorial : ℝ)) *
      ∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x

def HasCanonicalFreeEnergy (φ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ β ρ : ℝ, 0 < β → 0 < ρ →
    Tendsto (fun L : ℝ => L⁻¹ ^ 3 * Real.log (partition φ β L ⌊ρ * L ^ 3⌋₊))
      atTop (𝓝 (-β * f β ρ))

def MainStatement : Prop :=
  ∃ (φ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (I : Set ℝ) (βc : ℝ),
    Admissible φ ∧
    Asymptotics.IsLittleO atTop φ (fun r : ℝ => r ^ (-3 : ℤ)) ∧
    HasCanonicalFreeEnergy φ f ∧
    IsOpen I ∧ OrdConnected I ∧ I.Nonempty ∧ I ⊆ Ioi 0 ∧
    βc ∈ Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) ∧
    ∀ ρ ∈ I, ∃ dminus dplus : ℝ,
      HasDerivWithinAt (fun β => f β ρ) dminus (Iic βc) βc ∧
      HasDerivWithinAt (fun β => f β ρ) dplus (Ici βc) βc ∧
      dplus < dminus

def main_theorem_statement : Prop :=
  MainStatement

end ContinuumTemperature

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ContinuumTemperature.main_theorem_statement

end Problem

/- Formalization scope, from lean/docs/228.md: The formalization constructs one stable radial pair potential in three-dimensional continuum space with a divergent repulsive core and an integrable tail that is $o(r^{-3})$. Its canonical free energy exists for every positive inverse temperature and density. At one inverse temperature $\beta_c\in(1/2,3/2)$, the free energy has a strict finite jump between its one-sided derivatives with respect to inverse temperature, for every density in one nonempty open interval. The formalization constructs a bounded continuous stable radial pair potential in $\mathbb R^3$ satisfying $|\phi(r)|\le Cr^{-3-1/32}$ for $r\ge1$. There is a nonempty open interval of positive densities around $5p/3$, where $p$ is the unit-separated packing-density limit, on which the canonical free energy exists at every positive inverse temperature and has a strict downward derivative jump at one common $\beta_c\in[7/8,9/8]$. The earlier fixed-density statement at $5p/3$ is also retained. Both statements concern the derivative with respect to inverse temperature. -/
