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

- problem_id: ClassicalON
- collection: openai-math
- question_id: openai-math:215
- source: openai-math
- source_locator: lean/ComparatorChallenges/ClassicalON.lean#OAI.ClassicalON.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs the canonical continuum limit of the two-dimensional nearest-neighbor $`O(3)`$ model: a non-Gaussian local relativistic theory with a unique vacuum and a positive mass gap. For the square-lattice $`O(4)`$ model, determines the exact leading asymptotic of the full transfer gap, $`m_{\mathrm{lat}}(\beta)\sim32e^{\pi/4-1/2}\sqrt\beta\,e^{-\pi\beta}`$. The family also proves exponential spin-correlation decay for two-dimensional nearest-neighbor $`O(n)`$ models with n ≥ 3 at every positive temperature. ([Lean](lean/docs/215.md)) We prove exponential decay of two-point correlations for the classical nearest-neighbor $`O(n)`$ model on the square lattice, for every n ≥ 3 and every finite positive inverse temperature. The estimate is uniform over finite free-boundary subgraphs and bounded nonnegative edge strengths. This resolves positively the all-temperature exponential spin-decay conjecture for these models.
- notes: OpenAI math result family 215, Canonical $`O(3)`$ continuum limit and exact $`O(4)`$ mass asymptotics -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/215.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ClassicalON.main
- source_theorem_count: 1
- source_solution_module: OAI.Probability.ClassicalON.Main
- source_main_result: OAI.ClassicalON.main
- source_papers: preprints/Exponential-decay-in-two-dimensional-classical-On-models-September-23-2026/paper.pdf
- source_scope_note: lean/docs/215.md
- source_field: Probability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace ClassicalON

abbrev Site := ℤ × ℤ

def PositiveNeighbor (x y : Site) : Prop :=
  (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 ∧ y.2 = x.2 + 1)

structure LatticeGraph where
  vertices : Finset Site
  edges : Finset (vertices × vertices)
  nearest : ∀ e ∈ edges, PositiveNeighbor e.1.val e.2.val

abbrev Spin (n : ℕ) := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
abbrev Configuration (n : ℕ) (G : LatticeGraph) := G.vertices → Spin n

def sphereProbability (n : ℕ) : Measure (Spin n) :=
  let surface := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  (surface Set.univ)⁻¹ • surface

def referenceLaw (n : ℕ) (G : LatticeGraph) : Measure (Configuration n G) :=
  Measure.pi (fun _ => sphereProbability n)

def interaction (n : ℕ) (G : LatticeGraph) (b : G.edges → ℝ)
    (σ : Configuration n G) : ℝ :=
  ∑ e : G.edges, b e * ⟪(σ e.val.1).val, (σ e.val.2).val⟫_ℝ

def partition (n : ℕ) (G : LatticeGraph) (b : G.edges → ℝ) : ℝ :=
  ∫ σ, Real.exp (interaction n G b σ) ∂referenceLaw n G

def correlation (n : ℕ) (G : LatticeGraph) (b : G.edges → ℝ)
    (x y : G.vertices) : ℝ :=
  (∫ σ, ⟪(σ x).val, (σ y).val⟫_ℝ * Real.exp (interaction n G b σ)
    ∂referenceLaw n G) / partition n G b

def siteDistance (x y : Site) : ℝ :=
  Real.sqrt (((x.1 : ℝ) - (y.1 : ℝ)) ^ 2 + ((x.2 : ℝ) - (y.2 : ℝ)) ^ 2)

def ExponentialDecay : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (β : ℝ), 0 < β →
    ∃ A m : ℝ, 0 < m ∧ ∀ (G : LatticeGraph) (b : G.edges → ℝ),
      (∀ e, 0 ≤ b e ∧ b e ≤ β) → ∀ x y : G.vertices,
        0 ≤ correlation n G b x y ∧
          correlation n G b x y ≤ A * Real.exp (-m * siteDistance x.val y.val)

def main_statement : Prop :=
  ExponentialDecay

end ClassicalON

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ClassicalON.main_statement

end Problem

/- Formalization scope, from lean/docs/215.md: The formalized result proves exponential decay of spin correlations for the two-dimensional classical $O(n)$ model at every temperature when $n\ge3$. For each interaction bound $\beta>0$, constants $A$ and $m>0$ work for every finite square-lattice subgraph with free boundary and nonnegative edge strengths at most $\beta$: the correlation between sites $x,y$ is at most $Ae^{-m|x-y|}$. The infinite-volume limit and the separate $O(4)$ spectral-gap claim are not included. -/
