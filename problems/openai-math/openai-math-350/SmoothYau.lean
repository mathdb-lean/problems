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

- problem_id: SmoothYau
- collection: openai-math
- question_id: openai-math:350
- source: openai-math
- source_locator: lean/ComparatorChallenges/SmoothYau.lean#OAI.YauCounterexamples.sphere_three
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the sharp $`C\sqrt\lambda`$ upper bound for nodal length on every fixed smooth closed surface, completing Yau's conjecture there. The upper bound fails for fixed smooth metrics in dimensions three and four, including metrics on S3 arbitrarily close to round. In dimension five, nodal measure can grow faster than $`\lambda^{1/2+\varepsilon_0}`$ for some fixed $`\varepsilon_0\gt 0`$, ruling out even arbitrarily small power losses. ([Lean](lean/docs/350.md)) We prove that a nonzero real Laplace eigenfunction with eigenvalue λ &gt; 0 on a fixed smooth closed connected Riemannian surface has nodal length at most $`C\sqrt\lambda`$. Together with the known lower bound, this proves Yau's conjecture in this setting. We construct a smooth metric on the three-sphere, arbitrarily close to the round metric in the smooth topology, and a smooth metric on $`S^2\times\mathbb T^2`$ for which sequences of exact real Laplace eigenfunctions have unbounded nodal measure divided by the square root of the eigenvalue. Each sequence belongs to one fixed metric. Thus the upper-bound part of Yau's nodal conjecture fails for smooth metrics in dimensions three and four. We construct a smooth Riemannian metric on $`S^4\times S^1`$ and a sequence of real Laplace eigenfunctions whose nodal four-volume grows faster than $`\lambda^{1/2+\epsilon_0}`$ for one fixed $`\epsilon_0\gt 0`$. This disproves the smooth upper-bound assertion in Yau's nodal-set conjecture and the proposed bound with an arbitrarily small positive power loss.
- notes: OpenAI math result family 350, Yau’s nodal bounds: surfaces and higher dimensions -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/350.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.YauCounterexamples.sphere_three OAI.YauCounterexamples.sphere_two_torus_two
- source_theorem_count: 2
- source_solution_module: OAI.Geometry.SmoothYau.Main
- source_main_result: OAI.YauCounterexamples.sphere_two_torus_two
- source_papers: preprints/Sharp-nodal-length-on-smooth-surfaces-September-23-2026/paper.pdf preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf
- source_scope_note: lean/docs/350.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal


abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sphere (n : ℕ) := Metric.sphere (0 : Euclidean (n + 1)) 1
abbrev FourManifold := Sphere 2 × (Circle × Circle)
abbrev FourModel := Euclidean 2 × (Euclidean 1 × Euclidean 1)

instance torusChartedSpace : ChartedSpace (Euclidean 1 × Euclidean 1) (Circle × Circle) :=
  prodChartedSpace (Euclidean 1) Circle (Euclidean 1) Circle

instance torusIsManifold : IsManifold 𝓘(ℝ, Euclidean 1 × Euclidean 1) ∞ (Circle × Circle) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod Circle Circle

instance fourChartedSpace : ChartedSpace FourModel FourManifold :=
  prodChartedSpace (Euclidean 2) (Sphere 2) (Euclidean 1 × Euclidean 1) (Circle × Circle)

instance fourIsManifold : IsManifold 𝓘(ℝ, FourModel) ∞ FourManifold := by
  rw [show 𝓘(ℝ, FourModel) = 𝓘(ℝ, Euclidean 2).prod
    𝓘(ℝ, Euclidean 1 × Euclidean 1) from modelWithCornersSelf_prod]
  exact IsManifold.prod (Sphere 2) (Circle × Circle)

section Definitions
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Ordinary smooth positive-definite Riemannian metrics, with the existing tangent topology. -/
abbrev SmoothMetric (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] :=
  ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)

abbrev CoordIndex (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] := Fin (Module.finrank ℝ E)

/-- A coordinate vector, pushed from a chart back into the tangent bundle. -/
def coordinateVector (p : M) (y : E) (i : CoordIndex E) :
    TangentSpace 𝓘(ℝ, E) ((chartAt E p).symm y) :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y (Module.finBasis ℝ E i)

/-- Metric coefficients in a chart. Only values in the chart target are used. -/
def metricCoefficients (g : SmoothMetric E M) (p : M) (y : E) :
    Matrix (CoordIndex E) (CoordIndex E) ℝ :=
  fun i j => g.inner ((chartAt E p).symm y)
    (coordinateVector p y i) (coordinateVector p y j)

/-- The local coordinate formula det(g)^(-1/2) d_i(det(g)^(1/2) g^{ij} d_j u).
The chart at the evaluation point is used, so all derivatives are taken in
its open target. -/
def laplaceBeltrami (g : SmoothMetric E M) (u : M → ℝ) (x : M) : ℝ :=
  let c := chartAt E x
  let a := metricCoefficients g x
  let density := fun y => Real.sqrt (Matrix.det (a y))
  let u' := u ∘ c.symm
  (density (c x))⁻¹ * ∑ i, fderiv ℝ
    (fun y => density y * ∑ j, (a y)⁻¹ i j *
      fderiv ℝ u' y (Module.finBasis ℝ E j))
    (c x) (Module.finBasis ℝ E i)

/-- One compact-chart seminorm test for the usual smooth topology of metrics. -/
structure CoordinateTest (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M] where
  center : M
  compactSet : Set E
  isCompact : IsCompact compactSet
  inTarget : compactSet ⊆ (chartAt E center).target
  order : ℕ
  row : CoordIndex E
  column : CoordIndex E

/-- The finite compact-chart derivative tests defining a C∞ neighborhood.
A single positive tolerance suffices for the finitely many tests. -/
def IsSmoothNeighborhood (g₀ : SmoothMetric E M) (N : Set (SmoothMetric E M)) : Prop :=
  ∃ tests : List (CoordinateTest E M), ∃ ε : ℝ, 0 < ε ∧
    ∀ g : SmoothMetric E M,
      (∀ t ∈ tests, ∀ y ∈ t.compactSet,
        ‖iteratedFDeriv ℝ t.order
          (fun z => metricCoefficients g t.center z t.row t.column -
            metricCoefficients g₀ t.center z t.row t.column) y‖ < ε) → g ∈ N

/-- Hausdorff measure for the path distance of the actual Riemannian metric,
not the metric inherited from any ambient embedding. -/
def nodalMeasure [T3Space M] (g : SmoothMetric E M) (d : ℝ) (u : M → ℝ) : ℝ≥0∞ :=
  letI : RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  Measure.hausdorffMeasure d {x | u x = 0}

/-- The eigensequence belongs to one fixed metric and has finite nodal measure. -/
def HasUnboundedNodalRatio [T3Space M] (g : SmoothMetric E M) (d : ℕ) : Prop :=
  ∃ (u : ℕ → M → ℝ) (eigenvalue : ℕ → ℝ),
    (∀ j, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (u j) ∧ u j ≠ 0 ∧ 0 < eigenvalue j ∧
      (∀ x, -laplaceBeltrami g (u j) x = eigenvalue j * u j x) ∧
      nodalMeasure g (d - 1 : ℕ) (u j) ≠ (∞ : ℝ≥0∞)) ∧
    Tendsto eigenvalue atTop atTop ∧
    Tendsto (fun j => (nodalMeasure g (d - 1 : ℕ) (u j)).toReal / Real.sqrt (eigenvalue j))
      atTop atTop

end Definitions

/-- The round metric is the pullback of the Euclidean scalar product under
inclusion of the unit sphere. This predicate specifies exactly that tensor. -/
def IsRound (g : SmoothMetric (Euclidean 3) (Sphere 3)) : Prop :=
  ∀ (x : Sphere 3) (v w : TangentSpace 𝓘(ℝ, Euclidean 3) x),
    g.inner x v w = inner ℝ
      (mfderiv 𝓘(ℝ, Euclidean 3) 𝓘(ℝ, Euclidean 4)
        (fun y : Sphere 3 => (y : Euclidean 4)) x v)
      (mfderiv 𝓘(ℝ, Euclidean 3) 𝓘(ℝ, Euclidean 4)
        (fun y : Sphere 3 => (y : Euclidean 4)) x w)


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal


def sphere_three_statement : Prop :=
  ∀ (gRound : SmoothMetric (Euclidean 3) (Sphere 3)) (hRound : IsRound gRound),
    ∀ N : Set (SmoothMetric (Euclidean 3) (Sphere 3)),
      IsSmoothNeighborhood gRound N →
      ∃ g ∈ N, HasUnboundedNodalRatio g 3

def sphere_two_torus_two_statement : Prop :=
  ∃ g : SmoothMetric FourModel FourManifold,
      HasUnboundedNodalRatio g 4



end YauCounterexamples
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.YauCounterexamples.sphere_three_statement ∧
  _root_.OAI.YauCounterexamples.sphere_two_torus_two_statement

end Problem

/- Formalization scope, from lean/docs/350.md: Yau's nodal-set conjecture predicts nodal size of order $\sqrt\lambda$ for Laplace eigenfunctions of eigenvalue $\lambda$. The formalization proves the upper bound on every fixed smooth closed connected Riemannian surface: there is a surface-dependent constant $C$ such that the one-dimensional Hausdorff measure of the zero set of every nonzero real eigenfunction with $\lambda>0$ is at most $C\sqrt\lambda$. The known lower bound is not part of this selected statement. The formalized results contradict Yau's proposed $O(\sqrt\lambda)$ upper bound for nodal measure in dimensions three and four. On $S^3$, every prescribed smooth neighborhood of the round metric contains one fixed smooth metric with an eigenfunction sequence of unbounded nodal-measure ratio. A second fixed metric on $S^2\times T^2$ has the same property. In both cases the eigenvalues tend to infinity and the intrinsic nodal measures are finite. Yau's nodal upper-bound conjecture predicts that the nodal measure of an eigenfunction is bounded by a constant times the square root of its eigenvalue. The formalized counterexample fixes one smooth metric on $S^4\times S^1$ and a sequence of nonzero smooth eigenfunctions whose positive eigenvalues tend to infinity, while the intrinsic four-dimensional nodal measures divided by the square roots of the eigenvalues tend to infinity. The metric is fixed throughout the sequence. -/
