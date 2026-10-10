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

- problem_id: TamingCompatibility
- collection: openai-math
- question_id: openai-math:342
- source: openai-math
- source_locator: lean/ComparatorChallenges/TamingCompatibility.lean#OAI.TamingCompatibility.taming_implies_compatibility
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Donaldson's tamed-to-compatible conjecture: every smooth almost complex structure on a closed four-manifold that is tamed by a symplectic form admits a compatible symplectic form. The almost complex structure stays fixed; the form's cohomology class may change. ([Lean](lean/docs/342.md))
- notes: OpenAI math result family 342, Donaldson's tamed-to-compatible conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/342.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.TamingCompatibility.taming_implies_compatibility
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.TamingCompatibility.Main
- source_main_result: OAI.TamingCompatibility.taming_implies_compatibility
- source_scope_note: lean/docs/342.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open scoped Manifold ContDiff

namespace TamingCompatibility

abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev Model := 𝓘(ℝ, Space)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

abbrev TwoForm (X : Type*) [TopologicalSpace X] [ChartedSpace Space X] :=
  (x : X) → (TangentSpace Model x) [⋀^Fin 2]→L[ℝ] ℝ

structure AlmostComplexStructure (X : Type*) [TopologicalSpace X]
    [ChartedSpace Space X] [IsManifold Model ∞ X] where
  endomorphism : (x : X) → TangentSpace Model x →L[ℝ] TangentSpace Model x
  square : ∀ x v, endomorphism x (endomorphism x v) = -v
  smooth : ContMDiff Model.tangent Model.tangent ∞
    (fun p : TangentBundle Model X =>
      (⟨p.proj, endomorphism p.proj p.2⟩ : TangentBundle Model X))

def eval (α : TwoForm X) (x : X) (u v : TangentSpace Model x) : ℝ :=
  α x ![u, v]

noncomputable def pullback (α : TwoForm X) (f : Space → X) :
    Space → Space [⋀^Fin 2]→L[ℝ] ℝ :=
  fun y => (α (f y)).compContinuousLinearMap (mfderiv Model Model f y)

def IsSmooth (α : TwoForm X) : Prop :=
  ∀ (f : Space → X) (U : Set Space), IsOpen U →
    ContMDiffOn Model Model ∞ f U → ContDiffOn ℝ ∞ (pullback α f) U

def IsClosed (α : TwoForm X) : Prop :=
  ∀ (f : Space → X) (U : Set Space), IsOpen U →
    ContMDiffOn Model Model ∞ f U → ∀ y ∈ U,
      extDerivWithin (pullback α f) U y = 0

def IsNondegenerate (α : TwoForm X) : Prop :=
  ∀ x v, (∀ w, eval α x v w = 0) → v = 0

def IsSymplectic (α : TwoForm X) : Prop :=
  IsSmooth α ∧ IsClosed α ∧ IsNondegenerate α

def Tames (α : TwoForm X) (J : AlmostComplexStructure X) : Prop :=
  ∀ x v, v ≠ 0 → 0 < eval α x v (J.endomorphism x v)

def IsInvariant (α : TwoForm X) (J : AlmostComplexStructure X) : Prop :=
  ∀ x u v, eval α x (J.endomorphism x u) (J.endomorphism x v) = eval α x u v

def Compatible (α : TwoForm X) (J : AlmostComplexStructure X) : Prop :=
  Tames α J ∧ IsInvariant α J

def taming_implies_compatibility_statement : Prop :=
  ∀ {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X] [T2Space X] [SecondCountableTopology X] [CompactSpace X] [ConnectedSpace X] (J : AlmostComplexStructure X) (h : ∃ α : TwoForm X, IsSymplectic α ∧ Tames α J),
    ∃ η : TwoForm X, IsSymplectic η ∧ Compatible η J

end TamingCompatibility
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1} : Prop :=
  _root_.OAI.TamingCompatibility.taming_implies_compatibility_statement.{u_1}

end Problem

/- Formalization scope, from lean/docs/342.md: Donaldson's tamed-to-compatible conjecture asks whether an almost-complex structure tamed by a symplectic form also admits a compatible symplectic form. The formalized result establishes this for every closed connected smooth four-manifold, keeping the almost-complex structure fixed. No integrability assumption or prescribed cohomology class for the compatible form is required. -/
