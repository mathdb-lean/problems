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

- problem_id: PerceptronFreeEnergy
- collection: openai-math
- question_id: openai-math:222
- source: openai-math
- source_locator: lean/ComparatorChallenges/PerceptronFreeEnergy.lean#OAI.SphericalPerceptronFreeEnergy.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Determines finite-temperature variational free energies for Gaussian Ising perceptrons with bounded Borel log-potentials and Gaussian spherical perceptrons with bounded continuous potentials, at every positive pattern density. A spherical extension treats bi-orthogonally invariant disorder with compact limiting singular-value distributions and no outliers. At margin −1, the quadratic-penalty spherical model has a sharp feasibility threshold and limiting gap and force laws, with system size, zero temperature, and critical density taken in that order. ([Lean](lean/docs/222.md)) We determine the limiting free energy of the Ising perceptron with independent Gaussian patterns for every bounded Borel log-potential, at every fixed positive temperature and pattern density. We give an explicit variational formula for the limit and prove convergence in expectation and probability. We prove an exact variational formula for the limiting pressure of the spherical random perceptron with an arbitrary bounded continuous single-pattern potential. The formula holds at every fixed positive density and inverse temperature, with convergence in expectation and in probability.
- notes: OpenAI math result family 222, Perceptron free energies and microscopic jamming exponents -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/222.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SphericalPerceptronFreeEnergy.main
- source_theorem_count: 1
- source_solution_module: OAI.Probability.Perceptron.Main
- source_papers: preprints/The-free-energy-of-the-Ising-random-perceptron-September-24-2026/The-free-energy-of-the-Ising-random-perceptron-September-24-2026.pdf preprints/The-free-energy-of-the-spherical-random-perceptron-September-24-2026/The-free-energy-of-the-spherical-random-perceptron-September-24-2026.pdf
- source_scope_note: lean/docs/222.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptronFreeEnergy

abbrev Time := unitInterval
abbrev BrownianPath := C(ℝ≥0, ℝ)

instance : MeasurableSpace BrownianPath := borel BrownianPath
instance : BorelSpace BrownianPath := ⟨rfl⟩

abbrev Spin (N : ℕ) := EuclideanSpace ℝ (Fin N)

def patternCount (α : ℝ) (N : ℕ) : ℕ := ⌊α * (N : ℝ)⌋₊
abbrev Patterns (α : ℝ) (N : ℕ) := Fin (patternCount α N) → Fin N → ℝ

def patternLaw (α : ℝ) (N : ℕ) : Measure (Patterns α N) :=
  Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1

def unitSphereLaw (N : ℕ) : Measure (Metric.sphere (0 : Spin N) 1) :=
  let s := (volume : Measure (Spin N)).toSphere
  (s Set.univ)⁻¹ • s

def sphereLaw (N : ℕ) : Measure (Spin N) :=
  (unitSphereLaw N).map fun x => Real.sqrt (N : ℝ) • x.val

def patternField {α : ℝ} {N : ℕ} (g : Patterns α N)
    (a : Fin (patternCount α N)) (x : Spin N) : ℝ :=
  (∑ i : Fin N, g a i * x i) / Real.sqrt (N : ℝ)

def hamiltonian (α : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) (g : Patterns α N)
    (x : Spin N) : ℝ :=
  ∑ a : Fin (patternCount α N), φ (patternField g a x)

def pressure (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) (g : Patterns α N) : ℝ :=
  Real.log (∫ x, Real.exp (β * hamiltonian α φ N g x) ∂sphereLaw N) / (N : ℝ)

def expectedPressure (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) : ℝ :=
  ∫ g, pressure α β φ N g ∂patternLaw α N

structure Trial where
  toFun : Time → ℝ
  monotone : Monotone toFun
  measurable : Measurable toFun
  nonneg : ∀ t, 0 ≤ toFun t
  le_one : ∀ t, toFun t ≤ 1

instance : CoeFun Trial (fun _ => Time → ℝ) := ⟨Trial.toFun⟩

def timeLaw : Measure Time := Measure.comap Subtype.val volume

def tailIntegral (m : Trial) (t : Time) : ℝ :=
  ∫ s in Set.Ici t, m s ∂timeLaw

def entropy (m : Trial) : ℝ≥0∞ :=
  (∫⁻ t, (ENNReal.ofReal (tailIntegral m t))⁻¹ -
    (ENNReal.ofReal (1 - (t : ℝ)))⁻¹ ∂timeLaw) / 2

def brownianEval (t : ℝ≥0) (ω : BrownianPath) : ℝ := ω t

@[instance_reducible] def nullSigma (P : Measure BrownianPath) : MeasurableSpace BrownianPath :=
  MeasurableSpace.generateFrom {s | P s = 0}

@[instance_reducible] def usualBrownianSigma (P : Measure BrownianPath) (t : Time) :
    MeasurableSpace BrownianPath :=
  ⨅ s : {s : ℝ≥0 // (t : ℝ) < s},
    (⨆ r : {r : ℝ≥0 // r ≤ s.val},
      MeasurableSpace.comap (brownianEval r.val) (borel ℝ)) ⊔ nullSigma P

def Progressive (P : Measure BrownianPath) (v : Time → BrownianPath → ℝ) : Prop :=
  ∀ t : Time,
    @Measurable (Set.Iic t × BrownianPath) ℝ
      (MeasurableSpace.prod inferInstance (usualBrownianSigma P t)) (borel ℝ)
      (fun p => v p.1.val p.2)

def controlCost (P : Measure BrownianPath) (m : Trial)
    (v : Time → BrownianPath → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ t, ENNReal.ofReal (m t * v t ω ^ 2) ∂timeLaw ∂P

def controlPayoff (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (m : Trial)
    (v : Time → BrownianPath → ℝ) : ℝ :=
  (∫ ω, f (brownianEval 1 ω + ∫ t, m t * v t ω ∂timeLaw) ∂P) -
    (controlCost P m v).toReal / 2

def controlValue (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (m : Trial) : ℝ :=
  sSup {a | ∃ v : Time → BrownianPath → ℝ,
    Progressive P v ∧ controlCost P m v < ∞ ∧ a = controlPayoff P f m v}

def variationalValue (P : Measure BrownianPath) (α β : ℝ) (φ : ℝ →ᵇ ℝ) : EReal :=
  ⨅ m : Trial, ((α * controlValue P (β • φ) m : ℝ) : EReal) + (entropy m).toEReal

def main_statement : Prop :=
  ∀ (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (φ : ℝ →ᵇ ℝ),
    ∃ p : ℝ, variationalValue P α β φ = (p : EReal) ∧
      Tendsto (fun N : ℕ => expectedPressure α β φ (N + 1)) atTop (𝓝 p) ∧
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun N : ℕ => patternLaw α (N + 1)
          {g | ε < |pressure α β φ (N + 1) g - p|}) atTop (𝓝 0)

end SphericalPerceptronFreeEnergy

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SphericalPerceptronFreeEnergy.main_statement

end Problem

/- Formalization scope, from lean/docs/222.md: The linked formalization proves finiteness of the variational value used for the Ising random perceptron. For every nonnegative pattern density and every bounded continuous log-potential, the infimum over admissible overlap paths is a finite real number. This is a supporting well-definedness result. It does not assert convergence of the finite-system pressure or the paper's extension to all bounded Borel log-potentials. The formalization proves the variational formula for the spherical random perceptron's limiting pressure for every positive pattern density and inverse temperature and every bounded continuous single-pattern potential. It shows that the variational value is finite and that the pressure converges to it both in expectation and in probability. The linked spherical-field result supplies a supporting dual formula: finite hierarchy field values converge uniformly on compact parameter sets to an attained dual minimum, and the corresponding bounded stationary-field approximation holds for monotone overlap quantiles bounded away from one. -/
