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

- problem_id: SKValue
- collection: openai-math
- question_id: openai-math:281
- source: openai-math
- source_locator: lean/ComparatorChallenges/SKValue.lean#OAI.SKValue.value_consequences
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that QAOA approaches the ground-state energy of the Gaussian zero-field Sherrington–Kirkpatrick model when system size tends to infinity before circuit depth. For every accuracy, finite depth and deterministic angles independent of size and disorder achieve the required limiting expected energy per spin. This also yields leading-order optimal expected MaxCut values on large-degree random regular graphs, with size tending to infinity before degree. ([Lean](lean/docs/281.md)) We prove that the Quantum Approximate Optimization Algorithm (QAOA) approaches the ground-state energy per spin of the Gaussian zero-field Sherrington–Kirkpatrick model when system size tends to infinity first and circuit depth then increases. For every accuracy, some finite depth and deterministic angles, independent of system size and disorder, achieve that accuracy in the limiting expected energy per spin using the standard cost Hamiltonian and transverse-field mixer. This proves the eventual Parisi-optimality conjecture of Basso, Farhi, Marwaha, Villalonga, and Zhou in its fixed-parameter thermodynamic formulation. We give no quantitative bound on the required depth or efficient angle-selection procedure. We prove that every admissible integrable minimizer of the zero-temperature Parisi functional for the pure, zero-field Sherrington–Kirkpatrick model has full relative Stieltjes support on $`[0,1)`$. Thus its support has no gaps at any overlap scale below one. We use the covariance normalization $`\xi(t)=t^2/2`$.
- notes: OpenAI math result family 281, QAOA attains the SK optimum in the thermodynamic-first limit -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/281.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SKValue.value_consequences
- source_theorem_count: 1
- source_solution_module: OAI.Probability.SKValue.Main
- source_papers: preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf
- source_scope_note: lean/docs/281.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators

namespace SKValue

noncomputable def standardGaussian : Measure ℝ := gaussianReal 0 1

instance : IsProbabilityMeasure standardGaussian := by unfold standardGaussian; infer_instance

noncomputable def gaussianProduct (ι : Type) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι ↦ standardGaussian)
instance gaussianProduct_probability (ι : Type) [Fintype ι] :
    IsProbabilityMeasure (gaussianProduct ι) := by
  unfold gaussianProduct
  infer_instance

def coordinate (N : ℕ) (j : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  z ⟨j % (N+1), Nat.mod_lt _ (Nat.succ_pos _)⟩

noncomputable def stepSize (T : ℝ) (N : ℕ) : ℝ := T / N
noncomputable def meshTime (T : ℝ) (N j : ℕ) : ℝ := j * stepSize T N

noncomputable def euler (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (z : Fin (N+1) → ℝ) : ℕ → ℝ
  | 0 => 0
  | j+1 => euler T N γ u z j + Real.sqrt (stepSize T N) * coordinate N j z +
      stepSize T N * γ (meshTime T N j) * u (meshTime T N j) (euler T N γ u z j)

structure OrderParameter where
  coeff : ℝ → ℝ
  nonneg : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ coeff t
  monotone : MonotoneOn coeff (Ico (0 : ℝ) 1)
  rightContinuous : ∀ t ∈ Ico (0 : ℝ) 1, ContinuousWithinAt coeff (Ici t) t
  integrable : IntegrableOn coeff (Ioc (0 : ℝ) 1)

structure BrownianSpace where
  Ω : Type
  measurableSpace : MeasurableSpace Ω
  μ : @Measure Ω measurableSpace
  probability : @IsProbabilityMeasure Ω measurableSpace μ
  B : ℝ≥0 → Ω → ℝ
  measurable : ∀ t, @StronglyMeasurable Ω ℝ _ measurableSpace (B t)
  brownian : @IsBrownianReal Ω measurableSpace B μ

attribute [instance] BrownianSpace.measurableSpace BrownianSpace.probability

noncomputable def BrownianSpace.filtration (W : BrownianSpace) :
    Filtration ℝ≥0 W.measurableSpace := Filtration.natural W.B W.measurable

noncomputable def shiftedFiltration (W : BrownianSpace) (t : ℝ) :
    Filtration ℝ≥0 W.measurableSpace :=
  Filtration.natural (fun s ω ↦ W.B (Real.toNNReal t + s) ω - W.B (Real.toNNReal t) ω)
    (fun _ ↦ (W.measurable _).sub (W.measurable _))

def Admissible (W : BrownianSpace) (t : ℝ) (α : ℝ≥0 → W.Ω → ℝ) : Prop :=
  IsProgressive (shiftedFiltration W t) α ∧ ∀ s ω, |α s ω| ≤ 1

noncomputable def controlPayoff (W : BrownianSpace) (γ : OrderParameter)
    (t x : ℝ) (α : ℝ≥0 → W.Ω → ℝ) : ℝ :=
  ∫ ω, (|x + W.B 1 ω - W.B (Real.toNNReal t) ω +
    ∫ s in (0 : ℝ)..(1-t), γ.coeff (t+s) * α (Real.toNNReal s) ω| -
    (1/2 : ℝ) * ∫ s in (0 : ℝ)..(1-t), γ.coeff (t+s) * α (Real.toNNReal s) ω ^ 2) ∂W.μ

noncomputable def phi (W : BrownianSpace) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  sSup {r | ∃ α, Admissible W t α ∧ r = controlPayoff W γ t x α}

noncomputable def gradient (W : BrownianSpace) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  deriv (phi W γ t) x

noncomputable def curvature (W : BrownianSpace) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  deriv (gradient W γ t) x

noncomputable def parisi (W : BrownianSpace) (γ : OrderParameter) : ℝ :=
  phi W γ 0 0 - (1/2 : ℝ) * ∫ t in (0 : ℝ)..1, t * γ.coeff t

def IsMinimizer (W : BrownianSpace) (γ : OrderParameter) : Prop :=
  ∀ η : OrderParameter, parisi W γ ≤ parisi W η

def IsDiffusion (W : BrownianSpace) (γ : OrderParameter) (X : ℝ → W.Ω → ℝ) : Prop :=
  Adapted W.filtration (fun t ω ↦ X (min (t : ℝ) 1) ω) ∧
  (∀ᵐ ω ∂W.μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) 1) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      X t ω = W.B (Real.toNNReal t) ω +
        ∫ s in (0 : ℝ)..t, γ.coeff s * gradient W γ s (X s ω))

noncomputable def spin (b : Bool) : ℝ := if b then 1 else -1

noncomputable def hamiltonian (n : ℕ) (J : (Fin n × Fin n) → ℝ)
    (σ : Fin n → Bool) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ *
    ∑ i : Fin n, ∑ j : Fin n, if i < j then J (i,j) * spin (σ i) * spin (σ j) else 0

noncomputable def groundStateSequence (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∫ J, sSup (range (hamiltonian n J)) ∂gaussianProduct (Fin n × Fin n)

noncomputable def groundStateValue : ℝ := limUnder atTop groundStateSequence

noncomputable def gradientStopped (W : BrownianSpace) (γ : OrderParameter)
    (X : ℝ → W.Ω → ℝ) (U : W.Ω → ℝ) (t : ℝ≥0) (ω : W.Ω) : ℝ :=
  if (t : ℝ) < 1 then gradient W γ t (X t ω) else U ω

def ScalarValueConclusion (W : BrownianSpace) (γ : OrderParameter)
    (X : ℝ → W.Ω → ℝ) : Prop :=
  Tendsto groundStateSequence atTop (𝓝 groundStateValue) ∧
  ∃ U : W.Ω → ℝ,
    Martingale (gradientStopped W γ X U) W.filtration W.μ ∧
    (∀ᵐ ω ∂W.μ, |U ω| ≤ 1 ∧ (U ω)^2 = 1 ∧
      Tendsto (fun t ↦ gradient W γ t (X t ω)) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) ∧
    Tendsto (fun t ↦ ∫ ω, (gradient W γ t (X t ω) - U ω)^2 ∂W.μ)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) ∧
    groundStateValue = (∫ ω, |X 1 ω| ∂W.μ) - ∫ t in (0 : ℝ)..1, t * γ.coeff t ∧
    groundStateValue = ∫ ω, U ω * W.B 1 ω ∂W.μ ∧
    groundStateValue = ∫ t in (0 : ℝ)..1, ∫ ω, curvature W γ t (X t ω) ∂W.μ ∧
    IntervalIntegrable (fun t ↦ ∫ ω, curvature W γ t (X t ω) ∂W.μ) volume 0 1

noncomputable def eulerPath (W : BrownianSpace) (γ : OrderParameter) (T : ℝ) (N : ℕ)
    (z : Fin (N+1) → ℝ) (j : ℕ) : ℝ :=
  euler T N γ.coeff (gradient W γ) z j

noncomputable def rawCoefficient (W : BrownianSpace) (γ : OrderParameter)
    (T : ℝ) (N j : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  curvature W γ (meshTime T N j) (eulerPath W γ T N z j)

noncomputable def normalizer (W : BrownianSpace) (γ : OrderParameter)
    (T : ℝ) (N j : ℕ) : ℝ :=
  (Real.sqrt (∫ z, (rawCoefficient W γ T N j z)^2 ∂gaussianProduct (Fin (N+1))))⁻¹

noncomputable def gaussianIncrement (W : BrownianSpace) (γ : OrderParameter)
    (T : ℝ) (N j : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  normalizer W γ T N j * rawCoefficient W γ T N j z * coordinate N j z

noncomputable def roundedSign (W : BrownianSpace) (γ : OrderParameter)
    (T : ℝ) (N : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  Real.sign (gradient W γ T (eulerPath W γ T N z N) +
    2 * cdf standardGaussian (coordinate N N z) - 1)

noncomputable def coefficientA (W : BrownianSpace) (γ : OrderParameter)
    (T : ℝ) (N j : ℕ) : ℝ :=
  if j = 0 then 0 else
    ∫ z, roundedSign W γ T N z * gaussianIncrement W γ T N (j-1) z
      ∂gaussianProduct (Fin (N+1))

noncomputable def coefficientB (W : BrownianSpace) (γ : OrderParameter)
    (T : ℝ) (N i : ℕ) : ℝ :=
  ∫ z, roundedSign W γ T N z * coordinate N (i-1) z ∂gaussianProduct (Fin (N+1))

noncomputable def shiftedCoefficientSum (W : BrownianSpace) (γ : OrderParameter)
    (T : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N+1), coefficientA W γ T N j * coefficientB W γ T N (j+1)

def FiniteGaussianConclusion (W : BrownianSpace) (γ : OrderParameter)
    (X : ℝ → W.Ω → ℝ) (T : ℝ) : Prop :=
  (∀ᶠ N in atTop, ∀ j < N, 0 < normalizer W γ T N j) ∧
  Tendsto (shiftedCoefficientSum W γ T) atTop
    (𝓝 (∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ)) ∧
  Tendsto (fun S ↦ ∫ t in (0 : ℝ)..S, ∫ ω, curvature W γ t (X t ω) ∂W.μ)
    (𝓝[<] (1 : ℝ)) (𝓝 groundStateValue)

def value_consequences_statement : Prop :=
  (∀ (W : BrownianSpace) (γ : OrderParameter) (X : ℝ → W.Ω → ℝ),
      IsMinimizer W γ → IsDiffusion W γ X → ScalarValueConclusion W γ X) ∧
    (∀ (W : BrownianSpace) (γ : OrderParameter) (X : ℝ → W.Ω → ℝ) (T : ℝ),
      0 < T → T < 1 → IsMinimizer W γ → IsDiffusion W γ X →
      FiniteGaussianConclusion W γ X T) ∧
    (∀ (W : BrownianSpace) (γ : OrderParameter),
      IsMinimizer W γ → groundStateValue = parisi W γ)

end SKValue

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SKValue.value_consequences_statement

end Problem

/- Formalization scope, from lean/docs/281.md: The linked formalization supplies variational identities for the Gaussian zero-field Sherrington–Kirkpatrick ground-state energy used in the paper's QAOA argument. Conditional on an admissible Parisi minimizer and its associated diffusion, it proves convergence of the finite-system ground-state energy, identifies its limit with the Parisi value, and gives equivalent terminal-martingale and integrated-curvature formulas. It also proves convergence of finite Gaussian coefficient sums to the curvature integral, which approaches the ground-state value as the terminal time tends to one. The selected statement covers these value and approximation results; it does not itself assert convergence of QAOA circuit energies. The formalization proves that every admissible integrable minimizer of the zero-temperature Parisi functional for the pure zero-field Sherrington–Kirkpatrick model has full relative Stieltjes support on $[0,1)$. Equivalently, the order parameter increases strictly between every two overlap values below one, so its support has no gap. The covariance normalization is $\xi(t)=t^2/2$. The statement also constructs the associated diffusion and proves its selected self-consistency moment identities. It is conditional on the order parameter being a minimizer and does not separately assert existence of a minimizer. -/
