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

- problem_id: ConjugatePoints
- collection: openai-math
- question_id: openai-math:358
- source: openai-math
- source_locator: lean/ComparatorChallenges/ConjugatePoints.lean#OAI.ThreeManifold.main_theorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a closed connected orientable smooth three-manifold that admits a metric without conjugate points but no metric of nonpositive sectional curvature. This answers negatively, already in dimension three, whether the first metric-existence property implies the second. ([Lean](lean/docs/358.md)) We construct a closed connected orientable smooth three-manifold that admits a smooth Riemannian metric without conjugate points but admits no smooth Riemannian metric of nonpositive sectional curvature.
- notes: OpenAI math result family 358, A three-manifold without conjugate points or nonpositive curvature -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/358.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ThreeManifold.main_theorem
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.ConjugatePoints.ThreeManifold
- source_main_result: OAI.ThreeManifold.main_theorem
- source_papers: preprints/A-Three-Manifold-Without-Conjugate-Points-and-Without-a-Nonpositively-Curved-Metric-September-24-2026/paper.pdf
- source_scope_note: lean/docs/358.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff

namespace ThreeManifold

abbrev E3 := Fin 3 → ℝ
abbrev I3 := 𝓘(ℝ, E3)

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]

def OrientedAtlas : Prop :=
  ∀ (c d : OpenPartialHomeomorph M E3), c ∈ atlas E3 M → d ∈ atlas E3 M →
    ∀ x ∈ c.target, c.symm x ∈ d.source →
      0 < LinearMap.det (fderiv ℝ (d ∘ c.symm) x).toLinearMap

variable [IsManifold I3 ∞ M]

abbrev SmoothMetric (M : Type) [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] :=
  ContMDiffRiemannianMetric I3 ∞ E3 (fun x : M => TangentSpace I3 x)

def basisVector (i : Fin 3) : E3 := Pi.single i 1

def metricMatrix (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3) (x : E3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => g.inner (c.symm x)
    (mfderiv I3 I3 c.symm x (basisVector i))
    (mfderiv I3 I3 c.symm x (basisVector j))

def coordPartial (f : E3 → ℝ) (x : E3) (i : Fin 3) : ℝ :=
  fderiv ℝ f x (basisVector i)

def christoffel (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x : E3) (i j k : Fin 3) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin 3, (metricMatrix g c x)⁻¹ i l *
    (coordPartial (fun y => metricMatrix g c y l k) x j +
     coordPartial (fun y => metricMatrix g c y l j) x k -
     coordPartial (fun y => metricMatrix g c y j k) x l)

def connectionTerm (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x u v : E3) : E3 :=
  fun i => ∑ j : Fin 3, ∑ k : Fin 3, christoffel g c x i j k * u j * v k

def curvatureCoefficient (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x : E3) (l k i j : Fin 3) : ℝ :=
  coordPartial (fun y => christoffel g c y l j k) x i -
  coordPartial (fun y => christoffel g c y l i k) x j +
    ∑ a : Fin 3, (christoffel g c x l i a * christoffel g c x a j k -
      christoffel g c x l j a * christoffel g c x a i k)

def curvatureTerm (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x u v w : E3) : E3 :=
  fun l => ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
    curvatureCoefficient g c x l k i j * w k * u i * v j

def NonpositiveSectionalCurvature (g : SmoothMetric M) : Prop :=
  ∀ (c : OpenPartialHomeomorph M E3), c ∈ atlas E3 M →
    ∀ x ∈ c.target, ∀ u v : E3,
      (∑ i : Fin 3, ∑ j : Fin 3,
        metricMatrix g c x i j * curvatureTerm g c x u v v i * u j) ≤ 0

def alongDerivative (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x w : ℝ → E3) (s : ℝ) : E3 :=
  deriv w s + connectionTerm g c (x s) (deriv x s) (w s)

def IsGeodesicOn (g : SmoothMetric M) (γ : ℝ → M) (U : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ γ U ∧
    ∀ (c : OpenPartialHomeomorph M E3), c ∈ atlas E3 M →
      ∀ s ∈ U, γ s ∈ c.source →
        alongDerivative g c (c ∘ γ) (deriv (c ∘ γ)) s = 0

def fieldCoordinates (γ : ℝ → M) (J : ∀ s, TangentSpace I3 (γ s))
    (c : OpenPartialHomeomorph M E3) (s : ℝ) : E3 :=
  mfderiv I3 I3 c (γ s) (J s)

def IsJacobiFieldOn (g : SmoothMetric M) (γ : ℝ → M)
    (J : ∀ s, TangentSpace I3 (γ s)) (U : Set ℝ) : Prop :=
  ∀ (c : OpenPartialHomeomorph M E3), c ∈ atlas E3 M →
    ContDiffOn ℝ ∞ (fieldCoordinates γ J c) (U ∩ γ ⁻¹' c.source) ∧
    ∀ s ∈ U, γ s ∈ c.source →
      alongDerivative g c (c ∘ γ)
        (alongDerivative g c (c ∘ γ) (fieldCoordinates γ J c)) s +
      curvatureTerm g c (c (γ s)) (fieldCoordinates γ J c s)
        (deriv (c ∘ γ) s) (deriv (c ∘ γ) s) = 0

def NoConjugatePoints (g : SmoothMetric M) : Prop :=
  ∀ (U : Set ℝ), IsOpen U → OrdConnected U →
    ∀ (γ : ℝ → M), IsGeodesicOn g γ U →
      ∀ (J : ∀ s, TangentSpace I3 (γ s)), IsJacobiFieldOn g γ J U →
        ∀ a ∈ U, ∀ b ∈ U, a ≠ b → J a = 0 → J b = 0 → ∀ s ∈ U, J s = 0

def MainStatement : Prop :=
  ∃ (M : Type) (top : TopologicalSpace M),
    letI := top
    ∃ (_ : T2Space M) (_ : SecondCountableTopology M) (_ : CompactSpace M)
      (_ : ConnectedSpace M) (charts : ChartedSpace E3 M),
      letI := charts
      ∃ (smooth : IsManifold I3 ∞ M),
        letI := smooth
        OrientedAtlas (M := M) ∧
          (∃ g : SmoothMetric M, NoConjugatePoints g) ∧
          ¬ ∃ g : SmoothMetric M, NonpositiveSectionalCurvature g

def main_theorem_statement : Prop :=
  MainStatement

end ThreeManifold

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ThreeManifold.main_theorem_statement

end Problem

/- Formalization scope, from lean/docs/358.md: The formalized result separates absence of conjugate points from nonpositive sectional curvature. It constructs a closed connected orientable smooth three-manifold with a smooth Riemannian metric having no conjugate points, while the same manifold admits no smooth metric of everywhere nonpositive sectional curvature. The no-conjugate-points assertion ranges over all geodesics and tangent-bundle Jacobi fields, including constant geodesics and unbounded time intervals. The separate no-focal-points and CAT(0) consequences are not included. -/
