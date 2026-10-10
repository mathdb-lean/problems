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

- problem_id: SurfaceImmersion
- collection: openai-math
- question_id: openai-math:333
- source: openai-math
- source_locator: lean/ComparatorChallenges/SurfaceImmersion.lean#OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Every closed smooth Riemannian surface admits a smooth isometric immersion into ℝ4, resolving the closed-surface form of the four-dimensional isometric-immersion problem. This includes nonorientable surfaces and metrics of arbitrary Gaussian curvature. ([Lean](lean/docs/333.md)) Every closed smooth Riemannian surface admits a smooth isometric immersion into Euclidean four-space, without an orientability assumption. This resolves the closed-surface form of the classical four-dimensional isometric-immersion problem.
- notes: OpenAI math result family 333, Smooth isometric immersions of surfaces into ℝ<sup>4</sup> -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/333.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.SurfaceImmersion.Main
- source_papers: preprints/Smooth-isometric-immersions-of-closed-surfaces-into-Euclidean-four-space-September-23-2026/paper.pdf
- source_scope_note: lean/docs/333.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open Bundle Manifold
open scoped ContDiff

namespace ClosedSurfaceR4

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev planeModel := 𝓘(ℝ, Plane)
abbrev spaceModel := 𝓘(ℝ, Space)

section

variable (M : Type*) [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

abbrev SmoothMetric :=
  Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane
    (fun p : M => TangentSpace planeModel p)

def IsSmoothIsometricImmersion (g : SmoothMetric M) (F : M → Space) : Prop :=
  ContMDiff planeModel spaceModel ∞ F ∧
  ∀ (p : M) (v w : TangentSpace planeModel p),
    inner ℝ (mfderiv planeModel spaceModel F p v)
      (mfderiv planeModel spaceModel F p w) = g.inner p v w

end

namespace FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [SecondCountableTopology M]

/-- Every compact smooth Riemannian surface admits a smooth isometric immersion into Euclidean four-space. -/
def smooth_isometric_immersion_statement : Prop :=
  ∀ {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] (g : SmoothMetric M),
    ∃ F : M → Space, IsSmoothIsometricImmersion M g F

end FiniteOrderSmoothing
end ClosedSurfaceR4

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1} : Prop :=
  _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion_statement.{u_1}

end Problem

/- Formalization scope, from lean/docs/333.md: The formalization proves that every closed smooth Riemannian surface admits a smooth isometric immersion into $\mathbb R^4$. The differential preserves the Riemannian inner product on every tangent space. No orientability assumption is imposed, and the statement asks for an immersion rather than an embedding. -/
