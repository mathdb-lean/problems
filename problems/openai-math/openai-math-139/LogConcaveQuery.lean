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

- problem_id: LogConcaveQuery
- collection: openai-math
- question_id: openai-math:139
- source: openai-math
- source_locator: lean/ComparatorChallenges/LogConcaveQuery.lean#OAI.LogConcaveSampling.exact_source_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For C2 potentials with a supplied minimizer and $`I\preceq\nabla^2V\preceq2I`$, proves that sampling within total variation 1/10 requires only $`C_\varepsilon d^\varepsilon`$ exact value-and-gradient queries for every fixed ε &gt; 0. The bound holds on every run, with unrestricted computation between queries. A logarithmic lower bound also holds, so the optimal power-law exponent in this oracle model is zero. ([Lean](lean/docs/139.md)) For every fixed ε &gt; 0, we give a sampling algorithm using at most $`C_\varepsilon d^\varepsilon`$ exact first-order queries on every execution for C2 potentials on ℝd with a known minimizer and Hessian between Id and $`2I_d`$. The output has total-variation distance at most 1/10 from the target Gibbs law. Computation between queries is unrestricted. We also prove an $`\Omega(\log d)`$ query lower bound for arbitrary randomized adaptive algorithms, determining the optimal dimension exponent to be zero.
- notes: OpenAI math result family 139, Subpolynomial query complexity for log-concave sampling -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/139.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.LogConcaveSampling.exact_source_main
- source_theorem_count: 1
- source_solution_module: OAI.Probability.LogConcave.Main
- source_main_result: OAI.LogConcaveSampling.exact_source_main
- source_papers: preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf
- source_scope_note: lean/docs/139.md
- source_field: Probability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LogConcaveSampling

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Reply (d : ℕ) := ℝ × Point d
abbrev Transcript (d q : ℕ) := Fin q → Reply d

/-- Normalized twice continuously differentiable potentials with Hessian between the identity and twice the identity. -/
structure Admissible {d : ℕ} (V : Point d → ℝ) : Prop where
  smooth : ContDiff ℝ 2 V
  value_zero : V 0 = 0
  gradient_zero : gradient V 0 = 0
  hessian_bounds : ∀ x v : Point d,
    ‖v‖ ^ 2 ≤ inner ℝ v (fderiv ℝ (gradient V) x v) ∧
    inner ℝ v (fderiv ℝ (gradient V) x v) ≤ 2 * ‖v‖ ^ 2

/-- The unnormalized Gibbs density relative to Euclidean volume. -/
def gibbsDensity {d : ℕ} (V : Point d → ℝ) (x : Point d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-V x))

def partition {d : ℕ} (V : Point d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, gibbsDensity V x ∂volume

/-- The Gibbs probability law, normalized by its partition function. -/
def gibbs {d : ℕ} (V : Point d → ℝ) : Measure (Point d) :=
  (partition V)⁻¹ • volume.withDensity (gibbsDensity V)

def TVAtMost {E : Type*} [MeasurableSpace E]
    (μ ν : Measure E) (ε : ℝ) : Prop :=
  ∀ s : Set E, MeasurableSet s → |μ.real s - ν.real s| ≤ ε

def firstOrderReply {d : ℕ} (V : Point d → ℝ) (x : Point d) : Reply d :=
  (V x, gradient V x)

/-- Measurable adaptive queries and output, parametrized by private randomness. -/
structure OracleAlgorithm (Ω : Type*) [MeasurableSpace Ω] (d q : ℕ) where
  query : Fin q → Ω × Transcript d q → Point d
  query_measurable : ∀ i, Measurable (query i)
  output : Ω × Transcript d q → Point d
  output_measurable : Measurable output

def OracleAlgorithm.history {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (V : Point d → ℝ) (ω : Ω) : ℕ → Transcript d q
  | 0 => 0
  | n + 1 =>
      let h := A.history V ω n
      if hn : n < q then
        Function.update h ⟨n, hn⟩ (firstOrderReply V (A.query ⟨n, hn⟩ (ω, h)))
      else h

def OracleAlgorithm.run {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (V : Point d → ℝ) (ω : Ω) : Point d :=
  A.output (ω, A.history V ω q)

/-- A uniform sampler with a deterministic query budget on every execution and total-variation error at most one tenth. -/
def CanSample (d q : ℕ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
    (_ : IsProbabilityMeasure μ) (A : OracleAlgorithm Ω d q),
    ∀ V : Point d → ℝ, Admissible V →
      Measurable (A.run V) ∧ TVAtMost (μ.map (A.run V)) (gibbs V) (1 / 10)

/-- The smallest feasible integer query budget, or infinity when no budget is feasible. -/
def queryComplexity (d : ℕ) : ℕ∞ :=
  sInf ((fun q : ℕ => (q : ℕ∞)) '' {q | CanSample d q})

/-- The quantified dimension-exponent upper bound with every positive exponent slack. -/
def ExponentBound (γ : ℝ) : Prop :=
  0 ≤ γ ∧ ∀ ε : ℝ, 0 < ε → ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (queryComplexity d).toENNReal ≤ ENNReal.ofReal ((d : ℝ) ^ (γ + ε))

def gammaStar : ℝ := sInf {γ : ℝ | ExponentBound γ}

def exact_source_main_statement : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ d : ℕ, 2 ≤ d →
      (queryComplexity d).toENNReal ≤ ENNReal.ofReal (C * (d : ℝ) ^ ε)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ENNReal.ofReal (c * Real.log (d : ℝ)) ≤ (queryComplexity d).toENNReal) ∧
    gammaStar = 0

end LogConcaveSampling

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.LogConcaveSampling.exact_source_main_statement

end Problem

/- Formalization scope, from lean/docs/139.md: The formalized result determines the dimension exponent of exact value-and-gradient query complexity for well-conditioned log-concave sampling. For potentials with $V(0)=0$, $\nabla V(0)=0$, and $I\le\nabla^2V\le2I$, the least worst-case query budget achieving total-variation error at most $1/10$ is at most $C_\varepsilon d^\varepsilon$ for every $\varepsilon>0$, and at least $c\log d$ eventually. Hence the infimal polynomial exponent is zero. Algorithms may be measurable, randomized, and adaptive; arithmetic and bit costs are not bounded. -/
