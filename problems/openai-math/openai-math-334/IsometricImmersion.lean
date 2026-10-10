import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
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

- problem_id: IsometricImmersion
- collection: openai-math
- question_id: openai-math:334
- source: openai-math
- source_locator: lean/ComparatorChallenges/IsometricImmersion.lean#OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a smooth positive-definite metric on $`(-1,1)^2`$ for which no neighborhood of the origin admits a smooth isometric immersion into ℝ3. This answers the unrestricted smooth local isometric realization problem for surfaces negatively, even after shrinking the neighborhood. ([Lean](lean/docs/334.md)) We construct a smooth positive-definite Riemannian metric on $`(-1,1)^2`$ that agrees with the Euclidean metric to every order at the origin, yet no neighborhood of the origin admits a smooth isometric immersion into Euclidean three-space. This gives a negative answer to the unrestricted smooth local isometric realization problem for surfaces.
- notes: OpenAI math result family 334, A smooth surface metric with no local isometric immersion in ℝ<sup>3</sup> -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/334.md
- track: solved
- answer_shape: proof
- context_lemmas: coordinate_square_isOpen
- source_theorem: OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.IsometricImmersion.Main
- source_main_result: OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion
- source_papers: preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf
- source_scope_note: lean/docs/334.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open Set TopologicalSpace
open scoped ContDiff Topology Manifold Matrix

namespace SmoothLocal.Geometry

abbrev Coord := Fin 2 → ℝ

abbrev Ambient := EuclideanSpace ℝ (Fin 3)

def square : Set Coord := {p | ∀ i, p i ∈ Set.Ioo (-1 : ℝ) 1}

def LocalSmoothPositive (U : Opens Coord)
    (g : U → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (∀ i j, ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, ℝ) ∞ (fun p => g p i j)) ∧
    ∀ p, (g p).PosDef

end SmoothLocal.Geometry

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

theorem coordinate_square_isOpen : IsOpen square := by
  have heq : square = ⋂ i : Fin 2,
      (fun p : Coord => p i) ⁻¹' Ioo (-1 : ℝ) 1 := by
    ext p
    simp [square]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (continuous_apply i))

end SmoothLocal.ODE

namespace SmoothLocal.Geometry

def coordinateSquareOpen : Opens Coord :=
  ⟨square, SmoothLocal.ODE.coordinate_square_isOpen⟩

def exists_local_metric_without_local_immersion_statement : Prop :=
  ∃ g : coordinateSquareOpen → Matrix (Fin 2) (Fin 2) ℝ,
      LocalSmoothPositive coordinateSquareOpen g ∧
      ∀ U : Opens Coord, ∀ hUS : (U : Set Coord) ⊆ square,
        (0 : Coord) ∈ U → ∀ F : U → Ambient,
          ¬ (ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ F ∧
            ∀ p : U, ∀ v w : Coord,
              (inner ℝ : Ambient → Ambient → ℝ) (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) F p v)
                (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) F p w) =
                  v ⬝ᵥ (g ⟨p, hUS p.property⟩ *ᵥ w))

end SmoothLocal.Geometry

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion_statement

end Problem

/- Formalization scope, from lean/docs/334.md: The local isometric-immersion problem asks whether every smooth surface metric can be realized locally in Euclidean three-space. The formalized counterexample is a smooth positive-definite metric on $(-1,1)^2$ for which no neighborhood of the origin admits a smooth isometric immersion into $\mathbb R^3$. The obstruction applies to every smooth candidate map on every such neighborhood. -/
