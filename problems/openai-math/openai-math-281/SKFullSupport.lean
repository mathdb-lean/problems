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

- problem_id: SKFullSupport
- collection: openai-math
- question_id: openai-math:281
- source: openai-math
- source_locator: lean/ComparatorChallenges/SKFullSupport.lean#OAI.ZeroTemperatureSK.full_support
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that QAOA approaches the ground-state energy of the Gaussian zero-field Sherrington–Kirkpatrick model when system size tends to infinity before circuit depth. For every accuracy, finite depth and deterministic angles independent of size and disorder achieve the required limiting expected energy per spin. This also yields leading-order optimal expected MaxCut values on large-degree random regular graphs, with size tending to infinity before degree. ([Lean](lean/docs/281.md)) We prove that the Quantum Approximate Optimization Algorithm (QAOA) approaches the ground-state energy per spin of the Gaussian zero-field Sherrington–Kirkpatrick model when system size tends to infinity first and circuit depth then increases. For every accuracy, some finite depth and deterministic angles, independent of system size and disorder, achieve that accuracy in the limiting expected energy per spin using the standard cost Hamiltonian and transverse-field mixer. This proves the eventual Parisi-optimality conjecture of Basso, Farhi, Marwaha, Villalonga, and Zhou in its fixed-parameter thermodynamic formulation. We give no quantitative bound on the required depth or efficient angle-selection procedure. We prove that every admissible integrable minimizer of the zero-temperature Parisi functional for the pure, zero-field Sherrington–Kirkpatrick model has full relative Stieltjes support on $`[0,1)`$. Thus its support has no gaps at any overlap scale below one. We use the covariance normalization $`\xi(t)=t^2/2`$.
- notes: OpenAI math result family 281, QAOA attains the SK optimum in the thermodynamic-first limit -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/281.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ZeroTemperatureSK.full_support
- source_theorem_count: 1
- source_solution_module: OAI.Probability.SKSupport.Main
- source_papers: preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf
- source_scope_note: lean/docs/281.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace ZeroTemperatureSK

abbrev Time := Set.Ico (0 : ℝ) 1

def extend (γ : Time → ℝ) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ico (0 : ℝ) 1 then γ ⟨t, ht⟩ else 0

structure OrderParameter where
  val : Time → ℝ
  nonneg : ∀ t, 0 ≤ val t
  monotone : Monotone val
  right_continuous : ∀ t, ContinuousWithinAt val (Set.Ici t) t
  integrable : Integrable (extend val)

structure BrownianSystem (Ω : Type*) [MeasurableSpace Ω] where
  law : Measure Ω
  isProbability : IsProbabilityMeasure law
  B : ℝ≥0 → Ω → ℝ
  measurable : ∀ t, Measurable (B t)
  brownian : IsBrownianReal B law

variable {Ω : Type*} [MeasurableSpace Ω]

def incrementFiltration (W : BrownianSystem Ω) (t : ℝ≥0) :
    Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
  Filtration.natural (fun s ω => W.B (t + s) ω - W.B t ω)
    (fun s => ((W.measurable (t + s)).sub (W.measurable t)).stronglyMeasurable)

structure Control (W : BrownianSystem Ω) (t : ℝ≥0) where
  val : ℝ≥0 → Ω → ℝ
  progressive : IsProgressive (incrementFiltration W t) val
  bound : ∀ s ω, |val s ω| ≤ 1

def controlPayoff (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ)
    (α : Control W (Real.toNNReal t)) (ω : Ω) : ℝ :=
  |x + W.B 1 ω - W.B (Real.toNNReal t) ω +
      ∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω| -
    (1 / 2 : ℝ) * ∫ s in t..1, extend γ.val s * (α.val (Real.toNNReal (s - t)) ω)^2

def value (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  sSup (Set.range (fun α : Control W (Real.toNNReal t) =>
    ∫ ω, controlPayoff W γ t x α ω ∂W.law))

def gradient (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  deriv (value W γ t) x

def curvature (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  deriv (gradient W γ t) x

def parisi (W : BrownianSystem Ω) (γ : OrderParameter) : ℝ :=
  value W γ 0 0 - (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, t * extend γ.val t

def IsMinimizer (W : BrownianSystem Ω) (γ : OrderParameter) : Prop :=
  ∀ η : OrderParameter, parisi W γ ≤ parisi W η

def IsStieltjesMeasure (γ : OrderParameter) (μ : Measure Time) : Prop :=
  ∀ t : Time, μ (Set.Iic t) = ENNReal.ofReal (γ.val t)

def IsDiffusion (W : BrownianSystem Ω) (γ : OrderParameter)
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  IsProgressive (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)) X ∧
  (∀ᵐ ω ∂W.law, ContinuousOn (fun t : ℝ => X (Real.toNNReal t) ω) (Set.Icc 0 1) ∧
    X 0 ω = 0 ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      X (Real.toNNReal t) ω = W.B (Real.toNNReal t) ω +
        ∫ s in (0 : ℝ)..t, extend γ.val s *
          gradient W γ s (X (Real.toNNReal s) ω))

def squareMoment (W : BrownianSystem Ω) (γ : OrderParameter)
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, (gradient W γ t (X (Real.toNNReal t) ω))^2 ∂W.law

def FullSupportConclusion (W : BrownianSystem Ω) (γ : OrderParameter) : Prop :=
  (∃ μ : Measure Time, IsStieltjesMeasure γ μ) ∧
  (∃ X : ℝ≥0 → Ω → ℝ, IsDiffusion W γ X) ∧
  (∀ μ : Measure Time, IsStieltjesMeasure γ μ → μ.support = Set.univ) ∧
  (∀ a b : Time, a < b → γ.val a < γ.val b) ∧
  ∀ X : ℝ≥0 → Ω → ℝ, IsDiffusion W γ X → ∀ t : Time,
    squareMoment W γ X t = (t : ℝ) ∧
    (∫ ω, (curvature W γ t (X (Real.toNNReal t) ω))^2 ∂W.law) = 1

def full_support_statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω) (γ : OrderParameter) (hmin : IsMinimizer W γ),
    FullSupportConclusion W γ

end ZeroTemperatureSK

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1} : Prop :=
  _root_.OAI.ZeroTemperatureSK.full_support_statement.{u_1}

end Problem

/- Formalization scope, from lean/docs/281.md: The linked formalization supplies variational identities for the Gaussian zero-field Sherrington–Kirkpatrick ground-state energy used in the paper's QAOA argument. Conditional on an admissible Parisi minimizer and its associated diffusion, it proves convergence of the finite-system ground-state energy, identifies its limit with the Parisi value, and gives equivalent terminal-martingale and integrated-curvature formulas. It also proves convergence of finite Gaussian coefficient sums to the curvature integral, which approaches the ground-state value as the terminal time tends to one. The selected statement covers these value and approximation results; it does not itself assert convergence of QAOA circuit energies. The formalization proves that every admissible integrable minimizer of the zero-temperature Parisi functional for the pure zero-field Sherrington–Kirkpatrick model has full relative Stieltjes support on $[0,1)$. Equivalently, the order parameter increases strictly between every two overlap values below one, so its support has no gap. The covariance normalization is $\xi(t)=t^2/2$. The statement also constructs the associated diffusion and proves its selected self-consistency moment identities. It is conditional on the order parameter being a minimizer and does not separately assert existence of a minimizer. -/
/- A supporting-result comparison, not the paper's main theorem (lean/ComparatorChallenges/README.md). -/
