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

- problem_id: IsingFiniteness
- collection: openai-math
- question_id: openai-math:222
- source: openai-math
- source_locator: lean/ComparatorChallenges/IsingFiniteness.lean#OAI.IsingPerceptron.variationalValue_real_of_continuous
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Determines finite-temperature variational free energies for Gaussian Ising perceptrons with bounded Borel log-potentials and Gaussian spherical perceptrons with bounded continuous potentials, at every positive pattern density. A spherical extension treats bi-orthogonally invariant disorder with compact limiting singular-value distributions and no outliers. At margin −1, the quadratic-penalty spherical model has a sharp feasibility threshold and limiting gap and force laws, with system size, zero temperature, and critical density taken in that order. ([Lean](lean/docs/222.md)) We determine the limiting free energy of the Ising perceptron with independent Gaussian patterns for every bounded Borel log-potential, at every fixed positive temperature and pattern density. We give an explicit variational formula for the limit and prove convergence in expectation and probability. We prove an exact variational formula for the limiting pressure of the spherical random perceptron with an arbitrary bounded continuous single-pattern potential. The formula holds at every fixed positive density and inverse temperature, with convergence in expectation and in probability.
- notes: OpenAI math result family 222, Perceptron free energies and microscopic jamming exponents -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/222.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.IsingPerceptron.variationalValue_real_of_continuous
- source_theorem_count: 1
- source_solution_module: OAI.Probability.IsingPerceptron.VariationalFiniteness
- source_papers: preprints/The-free-energy-of-the-Ising-random-perceptron-September-24-2026/The-free-energy-of-the-Ising-random-perceptron-September-24-2026.pdf preprints/The-free-energy-of-the-spherical-random-perceptron-September-24-2026/The-free-energy-of-the-spherical-random-perceptron-September-24-2026.pdf
- source_scope_note: lean/docs/222.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

noncomputable section
namespace IsingPerceptron

def gaussianTransform (s d : ℝ) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  if d = 0 then ∫ z, U (x + Real.sqrt s * z) ∂gaussianReal 0 1
  else (Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z))
    ∂gaussianReal 0 1)) / d

structure Partition where
  levels : ℕ
  positive : 0 < levels
  cut : Fin (levels + 1) → ℝ
  ordered : StrictMono cut
  first : cut ⟨0, Nat.zero_lt_succ levels⟩ = 0
  last : cut ⟨levels, Nat.lt_succ_self levels⟩ = 1

structure FieldStep where
  partition : Partition
  value : Fin partition.levels → ℝ
  nonneg : ∀ i, 0 ≤ value i
  ordered : Monotone value

 
def stepAt (h : FieldStep) (i : ℕ) : ℝ :=
  if hi : i < h.partition.levels then h.value ⟨i, hi⟩ else 0

 

def stepFunction (h : FieldStep) (u : ℝ) : ℝ :=
  ∑ i : Fin h.partition.levels,
    if h.partition.cut i.castSucc < u ∧ u < h.partition.cut i.succ then h.value i else 0

 
def fieldRecursion (h : FieldStep) : ℝ :=
  let k := h.partition.levels
  let increments := List.ofFn (fun i : Fin k =>
    (stepAt h i - (if i.val = 0 then 0 else stepAt h (i.val - 1)),
      h.partition.cut i.castSucc))
  increments.foldr (fun sd U => gaussianTransform sd.1 sd.2 U)
    (fun x => Real.log (Real.cosh x) - stepAt h (k - 1) / 2) 0

def pathMeasure : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)

 
structure OverlapPath where
  val : ℝ →ₘ[pathMeasure] ℝ
  admissible : ∃ q : ℝ → ℝ,
    (q =ᵐ[pathMeasure] val) ∧ MonotoneOn q (Set.Ioo 0 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, q u ∈ Set.Icc (0 : ℝ) 1

 
def cellAverage (q : OverlapPath) (k i : ℕ) : ℝ :=
  (k : ℝ) * ∫ u in Set.Ioo ((i : ℝ) / k) (((i : ℝ) + 1) / k),
    q.val u ∂pathMeasure

 

def uniformPattern (f : ℝ → ℝ) (q : OverlapPath) (n : ℕ) : ℝ :=
  let k := n + 1
  let levelVal := fun i => if i < k then cellAverage q k i else 1
  let increments := List.ofFn (fun i : Fin (k + 1) =>
    (levelVal i - (if i.val = 0 then 0 else levelVal (i.val - 1)), (i : ℝ) / k))
  increments.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) f 0

 

def patternFunctional (f : ℝ → ℝ) (q : OverlapPath) : ℝ :=
  Filter.limUnder atTop (uniformPattern f q)

 

def isingEntropy (q : OverlapPath) : EReal :=
  ⨆ h : FieldStep,
    ((fieldRecursion h + (∫ u, stepFunction h u * q.val u ∂pathMeasure) / 2 : ℝ) : EReal)

def variationalValue (α : ℝ) (f : ℝ → ℝ) : EReal :=
  ⨅ q : OverlapPath, (α * patternFunctional f q : ℝ) + isingEntropy q

def variationalValue_real_of_continuous_statement : Prop :=
  ∀ {α : ℝ} (hα : 0 ≤ α) {f : ℝ → ℝ} (hf : Continuous f) (hbounded : ∃ K : ℝ, ∀ x, |f x| ≤ K),
    ∃ p : ℝ, variationalValue α f = (p : EReal)

end IsingPerceptron
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.IsingPerceptron.variationalValue_real_of_continuous_statement

end Problem

/- Formalization scope, from lean/docs/222.md: The linked formalization proves finiteness of the variational value used for the Ising random perceptron. For every nonnegative pattern density and every bounded continuous log-potential, the infimum over admissible overlap paths is a finite real number. This is a supporting well-definedness result. It does not assert convergence of the finite-system pressure or the paper's extension to all bounded Borel log-potentials. The formalization proves the variational formula for the spherical random perceptron's limiting pressure for every positive pattern density and inverse temperature and every bounded continuous single-pattern potential. It shows that the variational value is finite and that the pressure converges to it both in expectation and in probability. The linked spherical-field result supplies a supporting dual formula: finite hierarchy field values converge uniformly on compact parameter sets to an attained dual minimum, and the corresponding bounded stationary-field approximation holds for monotone overlap quantiles bounded away from one. -/
