import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.Basic
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

- problem_id: PlanarFirstPassage
- collection: openai-math
- question_id: openai-math:212
- source: openai-math
- source_locator: lean/ComparatorChallenges/PlanarFirstPassage.lean#OAI.PlanarFPP.manuscriptMain
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that planar first-passage percolation has no doubly infinite geodesic for iid nonnegative nonatomic edge weights when the minimum of four weights has finite second moment. For exponential weights, the limit shape is strictly convex with C1 boundary. Differentiability also holds for every Gamma law with positive shape and rate. ([Lean](lean/docs/212.md)) We prove that the limit shape of undirected nearest-neighbor first-passage percolation on ℤ2 with independent exponential edge weights is strictly convex and has a C1 boundary. This resolves the strict convexity and differentiability conjectures for the planar exponential model. More generally, we prove differentiability of the time-constant norm for every Gamma edge-weight law with positive shape and rate.
- notes: OpenAI math result family 212, Planar first-passage geometry and the absence of bigeodesics -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/212.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.PlanarFPP.manuscriptMain
- source_theorem_count: 1
- source_solution_module: OAI.Probability.FirstPassage.BoundaryCurve
- source_main_result: OAI.PlanarFPP.manuscriptMain
- source_papers: preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf
- source_scope_note: lean/docs/212.md
- source_field: Probability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace PlanarFPP

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

abbrev Vertex := ℤ × ℤ

abbrev Edge := Vertex × Bool

inductive Step where
  | east | west | north | south
  deriving DecidableEq

def Step.delta : Step → Vertex
  | .east => (1, 0)
  | .west => (-1, 0)
  | .north => (0, 1)
  | .south => (0, -1)

def Step.edge (p : Vertex) : Step → Edge
  | .east => (p, false)
  | .west => (p + (-1, 0), false)
  | .north => (p, true)
  | .south => (p + (0, -1), true)

def displacement (ds : List Step) : Vertex := (ds.map Step.delta).sum

def pathCost (τ : Edge → ℝ) (p : Vertex) : List Step → ℝ
  | [] => 0
  | d :: ds => τ (d.edge p) + pathCost τ (p + d.delta) ds

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def latticeFloor (v : Plane) : Vertex := (⌊v 0⌋, ⌊v 1⌋)

noncomputable def passageTime (τ : Edge → ℝ) (p q : Vertex) : ℝ :=
  sInf {t | ∃ ds : List Step, p + displacement ds = q ∧ pathCost τ p ds = t}

structure TimeConstantNorm (μ : Plane → ℝ) : Prop where
  nonneg : ∀ v, 0 ≤ μ v
  zero_iff : ∀ v, μ v = 0 ↔ v = 0
  triangle : ∀ v w, μ (v + w) ≤ μ v + μ w
  homogeneous : ∀ (a : ℝ) v, μ (a • v) = |a| * μ v

structure ExponentialEnvironment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Edge → Ω → ℝ) : Prop where
  probability : IsProbabilityMeasure P
  measurable : ∀ e, Measurable (τ e)
  independent : iIndepFun τ P
  marginal : ∀ e, Measure.map (τ e) P = expMeasure 1

def IsTimeConstant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Edge → Ω → ℝ) (μ : Plane → ℝ) : Prop :=
  ∀ v : Plane, ∀ᵐ ω ∂P,
    Tendsto (fun t : ℝ => passageTime (fun e => τ e ω) (0, 0)
      (latticeFloor (t • v)) / t) atTop (𝓝 (μ v))

def DifferentiableAwayFromOrigin (μ : Plane → ℝ) : Prop :=
  ∀ v : Plane, v ≠ 0 → ∃ ℓ : Plane →L[ℝ] ℝ, HasFDerivAt μ ℓ v

def UniqueNormalizedSupports (μ : Plane → ℝ) : Prop :=
  ∀ v : Plane, μ v = 1 → ∃! ℓ : Plane →L[ℝ] ℝ,
    ℓ v = 1 ∧ ∀ w, ℓ w ≤ μ w

def C1UnitSphere (μ : Plane → ℝ) : Prop :=
  ∀ v : Plane, μ v = 1 → ∃ U : Set Plane, IsOpen U ∧ v ∈ U ∧
    ∃ g : Plane → ℝ, ContDiffOn ℝ 1 g U ∧
      (∀ w ∈ U, μ w = 1 ↔ g w = 0) ∧
      ∀ w ∈ U, g w = 0 → ∃ ℓ : Plane →L[ℝ] ℝ,
        HasFDerivAt g ℓ w ∧ ℓ ≠ 0

def HasC1CurveChart (S : Set Plane) (v : Plane) : Prop :=
  ∃ U : Set Plane, IsOpen U ∧ v ∈ U ∧ v ∈ S ∧ ∃ γ : ℝ → Plane, ∃ θ : Plane → ℝ,
    ContDiff ℝ 1 γ ∧ ContinuousOn θ U ∧
    (∀ t, γ t ∈ S ∩ U) ∧ (∀ t, θ (γ t)=t) ∧
    (∀ z ∈ S ∩ U, γ (θ z)=z) ∧
    (∀ t, ∃ d : Plane, HasDerivAt γ d t ∧ d ≠ 0)

def manuscriptMain_statement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ) (henv : ExponentialEnvironment P τ),
    ∃ μ : Plane → ℝ, TimeConstantNorm μ ∧ IsTimeConstant P τ μ ∧
      DifferentiableAwayFromOrigin μ ∧ UniqueNormalizedSupports μ ∧ C1UnitSphere μ ∧
      (∀ v ∈ frontier {z | μ z ≤ 1}, ∃! L : Set Plane,
        ∃ g : Plane →L[ℝ] ℝ, g ≠ 0 ∧ (∀ z, μ z ≤ 1 → g z ≤ g v) ∧ L={z | g z=g v}) ∧
      (∀ v ∈ frontier {z | μ z ≤ 1}, HasC1CurveChart (frontier {z | μ z ≤ 1}) v)

end PlanarFPP

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.PlanarFPP.manuscriptMain_statement

end Problem

/- Formalization scope, from lean/docs/212.md: The formalization proves differentiability of the planar first-passage time-constant norm for independent Gamma edge weights of every positive shape and rate. The norm is differentiable away from the origin, and its unit sphere has a $C^1$ boundary. This includes the exponential model, for which the linked statement also gives a unique supporting line at every boundary point. The paper also claims strict convexity for the exponential limit shape. Strict convexity is outside these selected differentiability statements. -/
