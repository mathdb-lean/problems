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

- problem_id: CoulombCounterexample
- collection: openai-math
- question_id: openai-math:373
- source: openai-math
- source_locator: lean/ComparatorChallenges/CoulombCounterexample.lean#OAI.Problem356.coulomb_counterexample_and_equal_infima
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: An optimal three-particle Coulomb configuration need not be a deterministic function of the first particle, even for smooth identical spatial densities. The Monge and Kantorovich infima agree, but the Monge infimum is not attained. The same phenomenon occurs for every inverse-power Riesz exponent in each dimension at least two, with a suitable density in each case. ([Lean](lean/docs/373.md)) We construct a smooth compactly supported probability density on ℝ3, with a smooth compactly supported square root, for which the three-marginal Coulomb transport minimum is not attained by any pair of measure-preserving Borel maps. Nevertheless, the Monge and Kantorovich infima agree: we construct preserving maps whose costs approach the Kantorovich minimum. For every d ≥ 2 and s &gt; 0, we also construct a smooth identical marginal with the same nonattainment and equality-of-infima properties for the inverse-power interaction $`\sum_{i\lt j}|x_i-x_j|^{-s}`$ on ℝd.
- notes: OpenAI math result family 373, Nonattainment of the three-marginal Coulomb Monge problem -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/373.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Problem356.coulomb_counterexample_and_equal_infima
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.CoulombTransport.Main
- source_papers: preprints/A-counterexample-to-the-Monge-ansatz-for-the-three-marginal-Coulomb-cost-September-25-2026/paper.pdf
- source_scope_note: lean/docs/373.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

abbrev E3 := EuclideanSpace ℝ (Fin 3)

abbrev Triple := E3 × (E3 × E3)

def tripleFst (t : Triple) : E3 := t.1

def tripleSnd (t : Triple) : E3 := t.2.1

def tripleThd (t : Triple) : E3 := t.2.2

def invDistance (x y : E3) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖x - y‖)⁻¹

def coulombCost (t : Triple) : ℝ≥0∞ :=
  invDistance (tripleFst t) (tripleSnd t) +
    invDistance (tripleFst t) (tripleThd t) +
    invDistance (tripleSnd t) (tripleThd t)

def IsThreeCoupling (mu : Measure E3) (pi : Measure Triple) : Prop :=
  IsProbabilityMeasure pi ∧
    Measure.map tripleFst pi = mu ∧
    Measure.map tripleSnd pi = mu ∧
    Measure.map tripleThd pi = mu

def densityMeasure (rho : E3 → ℝ) : Measure E3 :=
  Measure.withDensity (volume : Measure E3) (fun x => ENNReal.ofReal (rho x))

def Preserves (mu : Measure E3) (T : E3 → E3) : Prop :=
  Measurable T ∧ Measure.map T mu = mu

def graphCost (mu : Measure E3) (T2 T3 : E3 → E3) : ℝ≥0∞ :=
  ∫⁻ x, coulombCost (x, (T2 x, T3 x)) ∂mu

def kantorovichValue (mu : Measure E3) : ℝ≥0∞ :=
  ⨅ (pi : Measure Triple), ⨅ (_h : IsThreeCoupling mu pi),
    ∫⁻ t, coulombCost t ∂pi

def mongeValue (mu : Measure E3) : ℝ≥0∞ :=
  ⨅ (T2 : E3 → E3), ⨅ (T3 : E3 → E3),
    ⨅ (_h2 : Preserves mu T2), ⨅ (_h3 : Preserves mu T3),
      graphCost mu T2 T3

def IsSmoothCompactProbabilityDensity (rho : E3 → ℝ) : Prop :=
  (∀ x, 0 ≤ rho x) ∧
    ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) rho ∧
    HasCompactSupport rho ∧
    ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (fun x : E3 => Real.sqrt (rho x)) ∧
    HasCompactSupport (fun x : E3 => Real.sqrt (rho x)) ∧
    (∫ x : E3, rho x ∂(volume : Measure E3)) = 1

def KantorovichAttained (mu : Measure E3) : Prop :=
  ∃ pi : Measure Triple,
    IsThreeCoupling mu pi ∧
      (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu

def NoMongeOptimizer (mu : Measure E3) : Prop :=
  ∀ T2 T3 : E3 → E3,
    Preserves mu T2 → Preserves mu T3 →
      kantorovichValue mu < graphCost mu T2 T3

def FiniteMongeApproximation (mu : Measure E3) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ T2 T3 : E3 → E3,
      Preserves mu T2 ∧
      Preserves mu T3 ∧
      graphCost mu T2 T3 < ⊤ ∧
      graphCost mu T2 T3 ≤
        kantorovichValue mu + ENNReal.ofReal epsilon

def HasCoulombCounterexample (rho : E3 → ℝ) : Prop :=
  IsSmoothCompactProbabilityDensity rho ∧
    IsProbabilityMeasure (densityMeasure rho) ∧
    kantorovichValue (densityMeasure rho) < ⊤ ∧
    KantorovichAttained (densityMeasure rho) ∧
    NoMongeOptimizer (densityMeasure rho)

def HasFullCoulombConclusion (rho : E3 → ℝ) : Prop :=
  HasCoulombCounterexample rho ∧
    mongeValue (densityMeasure rho) =
      kantorovichValue (densityMeasure rho) ∧
    FiniteMongeApproximation (densityMeasure rho)

def coulomb_counterexample_and_equal_infima_statement : Prop :=
  ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho

end Problem356

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Problem356.coulomb_counterexample_and_equal_infima_statement

end Problem

/- Formalization scope, from lean/docs/373.md: The Monge ansatz asks whether an optimal multi-marginal transport plan can be induced by maps from one marginal. For the three-marginal Coulomb cost in $\mathbb R^3$, the formalization constructs a smooth compactly supported probability density, with smooth compactly supported square root, for which no pair of measure-preserving Borel maps attains the Kantorovich minimum. Nevertheless, the Monge and Kantorovich infima are equal: preserving maps with finite costs approach the minimum. This is the three-dimensional Coulomb result; the paper's inverse-power extensions in every dimension are outside this statement. -/
