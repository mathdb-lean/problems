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

- problem_id: RadialTransition
- collection: openai-math
- question_id: openai-math:228
- source: openai-math
- source_locator: lean/ComparatorChallenges/RadialTransition.lean#OAI.RadialTransition.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs stable distance-dependent pair interactions for three-dimensional classical particles with a first-order phase transition: the canonical free energy has a derivative jump at one inverse temperature throughout an open density interval. One potential has a divergent repulsive core; another is bounded and continuous with an integrable power-law tail, realizing the type of transition sought in Simon's continuum problem. ([Lean](lean/docs/228.md)) We construct a stable radial pair potential in three dimensions whose canonical free energy has a strict downward derivative jump at one common finite positive inverse temperature throughout an open interval of positive densities. The potential has a divergent repulsive core, a nontrivial attractive interval, and an integrable tail satisfying $`\phi(r)=o(r^{-3})`$. Its free-cube canonical free energy is finite at every positive inverse temperature and density. We construct a bounded, continuous, stable radial pair potential in three dimensions with $`|\phi(r)|\le Cr^{-3-1/32}`$ for r ≥ 1. Throughout an open interval of positive densities, its canonical thermodynamic free energy is finite at every positive inverse temperature and has a strict downward derivative jump at one common finite positive inverse temperature.
- notes: OpenAI math result family 228, Continuum phase transitions for radial pair potentials -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/228.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.RadialTransition.main
- source_theorem_count: 1
- source_solution_module: OAI.Probability.RadialTransition.Main
- source_main_result: OAI.RadialTransition.main
- source_papers: preprints/A-continuum-temperature-singularity-for-a-radial-pair-potential-September-24-2026/paper.pdf preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf
- source_scope_note: lean/docs/228.md
- source_field: Probability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open scoped BigOperators NNReal
open Filter MeasureTheory Set

namespace RadialTransition

abbrev Position := EuclideanSpace ℝ (Fin 3)
abbrev Potential := ℝ≥0 → ℝ

def cube (L : ℝ) : Set Position :=
  {x | ∀ k : Fin 3, 0 ≤ x k ∧ x k ≤ L}

def configurationCube (L : ℝ) (N : ℕ) : Set (Fin N → Position) :=
  {x | ∀ i : Fin N, x i ∈ cube L}

def energy (φ : Potential) {N : ℕ} (x : Fin N → Position) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N with i < j, φ (nndist (x i) (x j))

def partition (φ : Potential) (L : ℝ) (N : ℕ) (β : ℝ) : ℝ :=
  (N.factorial : ℝ)⁻¹ *
    ∫ x in configurationCube L N, Real.exp (-β * energy φ x)

def packingNumber (L : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ X : Finset Position, X.card = n ∧
    (∀ x ∈ X, x ∈ cube L) ∧
    (∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y)}

def IsPackingDensity (p : ℝ) : Prop :=
  Tendsto (fun L : ℝ => (packingNumber L : ℝ) / L ^ 3) atTop (nhds p)

def IsBoundedPotential (φ : Potential) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ≥0, |φ r| ≤ M

def StableWith (φ : Potential) (B : ℝ) : Prop :=
  ∀ (N : ℕ) (x : Fin N → Position), -(B * N) ≤ energy φ x

def AlgebraicDecayWith (φ : Potential) (C : ℝ) : Prop :=
  ∀ r : ℝ≥0, 1 ≤ r → |φ r| ≤ C * (r : ℝ) ^ (-(3 : ℝ) - 1 / 32)

def IsCanonicalFreeEnergy (φ : Potential) (ρ : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ β : ℝ, 0 < β →
    Tendsto (fun L : ℝ =>
      -(Real.log (partition φ L ⌊ρ * L ^ 3⌋₊ β) / (β * L ^ 3)))
      atTop (nhds (f β))

def StrictTemperatureCorner (f : ℝ → ℝ) (βc : ℝ) : Prop :=
  ∃ dLeft dRight : ℝ,
    HasDerivWithinAt f dLeft (Iic βc) βc ∧
    HasDerivWithinAt f dRight (Ici βc) βc ∧
    dRight < dLeft ∧ ¬DifferentiableAt ℝ f βc

def main_statement : Prop :=
  ∃ (p : ℝ) (φ : Potential) (B C : ℝ) (f : ℝ → ℝ) (βc : ℝ),
      0 < p ∧ IsPackingDensity p ∧
      IsBoundedPotential φ ∧ Continuous φ ∧
      0 < B ∧ 0 < C ∧ StableWith φ B ∧ AlgebraicDecayWith φ C ∧
      IsCanonicalFreeEnergy φ (5*p/3) f ∧
      βc ∈ Icc (7/8:ℝ) (9/8) ∧ StrictTemperatureCorner f βc

end RadialTransition

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.RadialTransition.main_statement

end Problem

/- Formalization scope, from lean/docs/228.md: The formalization constructs one stable radial pair potential in three-dimensional continuum space with a divergent repulsive core and an integrable tail that is $o(r^{-3})$. Its canonical free energy exists for every positive inverse temperature and density. At one inverse temperature $\beta_c\in(1/2,3/2)$, the free energy has a strict finite jump between its one-sided derivatives with respect to inverse temperature, for every density in one nonempty open interval. The formalization constructs a bounded continuous stable radial pair potential in $\mathbb R^3$ satisfying $|\phi(r)|\le Cr^{-3-1/32}$ for $r\ge1$. There is a nonempty open interval of positive densities around $5p/3$, where $p$ is the unit-separated packing-density limit, on which the canonical free energy exists at every positive inverse temperature and has a strict downward derivative jump at one common $\beta_c\in[7/8,9/8]$. The earlier fixed-density statement at $5p/3$ is also retained. Both statements concern the derivative with respect to inverse temperature. -/
