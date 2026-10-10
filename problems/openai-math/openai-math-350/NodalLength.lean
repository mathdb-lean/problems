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

- problem_id: NodalLength
- collection: openai-math
- question_id: openai-math:350
- source: openai-math
- source_locator: lean/ComparatorChallenges/NodalLength.lean#OAI.SharpNodal.Main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the sharp $`C\sqrt\lambda`$ upper bound for nodal length on every fixed smooth closed surface, completing Yau's conjecture there. The upper bound fails for fixed smooth metrics in dimensions three and four, including metrics on S3 arbitrarily close to round. In dimension five, nodal measure can grow faster than $`\lambda^{1/2+\varepsilon_0}`$ for some fixed $`\varepsilon_0\gt 0`$, ruling out even arbitrarily small power losses. ([Lean](lean/docs/350.md)) We prove that a nonzero real Laplace eigenfunction with eigenvalue λ &gt; 0 on a fixed smooth closed connected Riemannian surface has nodal length at most $`C\sqrt\lambda`$. Together with the known lower bound, this proves Yau's conjecture in this setting. We construct a smooth metric on the three-sphere, arbitrarily close to the round metric in the smooth topology, and a smooth metric on $`S^2\times\mathbb T^2`$ for which sequences of exact real Laplace eigenfunctions have unbounded nodal measure divided by the square root of the eigenvalue. Each sequence belongs to one fixed metric. Thus the upper-bound part of Yau's nodal conjecture fails for smooth metrics in dimensions three and four. We construct a smooth Riemannian metric on $`S^4\times S^1`$ and a sequence of real Laplace eigenfunctions whose nodal four-volume grows faster than $`\lambda^{1/2+\epsilon_0}`$ for one fixed $`\epsilon_0\gt 0`$. This disproves the smooth upper-bound assertion in Yau's nodal-set conjecture and the proposed bound with an arbitrarily small positive power loss.
- notes: OpenAI math result family 350, Yau’s nodal bounds: surfaces and higher dimensions -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/350.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SharpNodal.Main
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.NodalLength.Main
- source_papers: preprints/Sharp-nodal-length-on-smooth-surfaces-September-23-2026/paper.pdf preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf
- source_scope_note: lean/docs/350.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal

abbrev Plane := EuclideanSpace ℝ (Fin 2)

variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Plane) x)]

def coordinateMetric (x : M) (y : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => inner ℝ
    (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (chartAt Plane x).symm y
      (EuclideanSpace.single i 1))
    (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (chartAt Plane x).symm y
      (EuclideanSpace.single j 1))

def coordinateDensity (x : M) (y : Plane) : ℝ :=
  Real.sqrt (coordinateMetric x y).det

def coordPartial (f : Plane → ℝ) (i : Fin 2) (y : Plane) : ℝ :=
  fderiv ℝ f y (EuclideanSpace.single i 1)

def laplaceBeltrami (u : M → ℝ) (x : M) : ℝ :=
  (coordinateDensity x (chartAt Plane x x))⁻¹ *
    ∑ i : Fin 2, coordPartial (fun y => coordinateDensity x y *
      ∑ j : Fin 2, ((coordinateMetric x y)⁻¹ i j) *
        coordPartial (u ∘ (chartAt Plane x).symm) j y) i (chartAt Plane x x)

def nodalSet (u : M → ℝ) : Set M := {x | u x = 0}

def nodalLength (u : M → ℝ) : ℝ≥0∞ :=
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  Measure.hausdorffMeasure 1 (nodalSet u)

def MainStatement (M : Type*) [MetricSpace M] [ChartedSpace Plane M]
    [IsManifold 𝓘(ℝ, Plane) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Plane) x)] : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℝ), 0 < lam → ∀ (u : M → ℝ),
    ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ) ∞ u → u ≠ 0 →
    (∀ x, -laplaceBeltrami u x = lam * u x) →
    nodalLength u ≤ ENNReal.ofReal (C * Real.sqrt lam)

def Main_statement : Prop :=
  ∀ {M : Type*} [MetricSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ, Plane) ∞ M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Plane) x)] [CompactSpace M] [ConnectedSpace M] [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane
      (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] [IsRiemannianManifold 𝓘(ℝ,Plane) M],
    MainStatement M

end SharpNodal

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1} : Prop :=
  _root_.OAI.SharpNodal.Main_statement.{u_1}

end Problem

/- Formalization scope, from lean/docs/350.md: Yau's nodal-set conjecture predicts nodal size of order $\sqrt\lambda$ for Laplace eigenfunctions of eigenvalue $\lambda$. The formalization proves the upper bound on every fixed smooth closed connected Riemannian surface: there is a surface-dependent constant $C$ such that the one-dimensional Hausdorff measure of the zero set of every nonzero real eigenfunction with $\lambda>0$ is at most $C\sqrt\lambda$. The known lower bound is not part of this selected statement. The formalized results contradict Yau's proposed $O(\sqrt\lambda)$ upper bound for nodal measure in dimensions three and four. On $S^3$, every prescribed smooth neighborhood of the round metric contains one fixed smooth metric with an eigenfunction sequence of unbounded nodal-measure ratio. A second fixed metric on $S^2\times T^2$ has the same property. In both cases the eigenvalues tend to infinity and the intrinsic nodal measures are finite. Yau's nodal upper-bound conjecture predicts that the nodal measure of an eigenfunction is bounded by a constant times the square root of its eigenvalue. The formalized counterexample fixes one smooth metric on $S^4\times S^1$ and a sequence of nonzero smooth eigenfunctions whose positive eigenvalues tend to infinity, while the intrinsic four-dimensional nodal measures divided by the square roots of the eigenvalues tend to infinity. The metric is fixed throughout the sequence. -/
