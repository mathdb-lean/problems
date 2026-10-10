import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.MetricSpace.Isometry
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

- problem_id: TingleySphereIsometry
- collection: openai-math
- question_id: openai-math:322
- source: openai-math
- source_locator: lean/ComparatorChallenges/TingleySphereIsometry.lean#OAI.Tingley.tingley_sphere_isometry_full
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves Tingley's problem: every surjective isometry between the unit spheres of nonzero real Banach spaces extends uniquely to a surjective real-linear isometry of the whole spaces. No dimension restriction is imposed, so the metric geometry of the unit sphere determines the Banach space up to linear isometry. ([Lean](lean/docs/322.md)) Every surjective isometry between the unit spheres of real Banach spaces extends uniquely to a surjective real-linear isometry, giving an affirmative solution to Tingley's problem. If distances between different radii are not preserved, we realize the positive maximal defect in a possibly enlarged pair of Banach spaces. We then align extremal chords using common supports and Darbo's fixed-point theorem and obtain a contradiction from support and convexity estimates.
- notes: OpenAI math result family 322, Tingley’s sphere-isometry problem -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/322.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Tingley.tingley_sphere_isometry_full
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.SphereIsometry.Main
- source_main_result: OAI.Tingley.tingley_sphere_isometry_full
- source_papers: preprints/A-positive-solution-to-Tingleys-problem-September-23-2026/paper.pdf
- source_scope_note: lean/docs/322.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

namespace Tingley

universe u v

abbrev UnitSphere (X : Type u) [NormedAddCommGroup X] := {x : X // ‖x‖ = 1}

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def normalize (x : X) (hx : x ≠ 0) : UnitSphere X :=
  ⟨‖x‖⁻¹ • x, norm_smul_inv_norm hx⟩

/-- Radial formula, surjectivity, and uniqueness among all real-linear extensions. -/
def tingley_sphere_isometry_full_statement : Prop :=
  ∀ {X : Type u} {Y : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] [Nontrivial X] [Nontrivial Y] (f : UnitSphere X → UnitSphere Y) (hf : Isometry f) (hs : Function.Surjective f),
    ∃ T : X ≃ₗᵢ[ℝ] Y,
      (∀ u : UnitSphere X, T (u : X) = (f u : Y)) ∧
      T 0 = 0 ∧
      (∀ x : X, ∀ hx : x ≠ 0, T x = ‖x‖ • (f (normalize x hx) : Y)) ∧
      Function.Surjective T ∧
      (∀ L : X →ₗ[ℝ] Y, (∀ u : UnitSphere X, L (u : X) = (f u : Y)) →
        L = T.toLinearEquiv.toLinearMap)

end Tingley

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u, v} : Prop :=
  _root_.OAI.Tingley.tingley_sphere_isometry_full_statement.{u, v}

end Problem

/- Formalization scope, from lean/docs/322.md: Tingley's problem asks whether a surjective isometry between the unit spheres of Banach spaces extends to a linear isometry of the spaces. The formalized result gives a unique surjective real-linear isometric extension for arbitrary nonzero real Banach spaces, with no finite-dimensionality, separability, reflexivity, or convexity assumptions. For complex spaces viewed as real spaces, the conclusion is real linearity rather than complex linearity. -/
