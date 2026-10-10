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

- problem_id: FinitisticAsymmetry
- collection: openai-math
- question_id: openai-math:198
- source: openai-math
- source_locator: lean/ComparatorChallenges/FinitisticAsymmetry.lean#OAI.LittleFinitistic.extreme_left_right_asymmetry
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a finite-dimensional complex algebra whose finite-dimensional modules have unbounded finite projective dimensions. This disproves the little finitistic-dimension conjecture. ([Lean](lean/docs/198.md)) We construct a finite-dimensional complex algebra whose finite-dimensional modules have unbounded finite projective dimensions. This disproves the little finitistic-dimension conjecture.
- notes: OpenAI math result family 198, A counterexample to finitistic-dimension finiteness -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/198.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.LittleFinitistic.extreme_left_right_asymmetry
- source_theorem_count: 1
- source_solution_module: OAI.Algebra.FinitisticAsymmetry.Main
- source_main_result: OAI.LittleFinitistic.extreme_left_right_asymmetry
- source_papers: preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf
- source_scope_note: lean/docs/198.md
- source_field: Algebra
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open CategoryTheory

namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]

attribute [-instance] CompletePartialOrder.toSupSet in
def littleFinitisticDimension : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{u} A) (_ : Module.Finite A M) (_ : projectiveDimension M < ⊤),
    projectiveDimension M

def bigFinitisticDimension : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{u} A) (_ : projectiveDimension M < ⊤), projectiveDimension M

def InjectivesGenerate : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} A)
  ∀ (P : ObjectProperty (DerivedCategory (ModuleCat.{u} A))),
    P.IsClosedUnderIsomorphisms → P.IsTriangulated →
    (∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I)) →
    (∀ (M : ModuleCat.{u} A), Injective M →
      P ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) →
    ∀ X, P X

def extreme_left_right_asymmetry_statement : Prop :=
  ∃ (Λ : Type) (_ : Ring Λ) (_ : Algebra ℂ Λ),
      FiniteDimensional ℂ Λ ∧
      littleFinitisticDimension Λ = ⊤ ∧ bigFinitisticDimension Λ = ⊤ ∧
      littleFinitisticDimension Λᵐᵒᵖ = 0 ∧ bigFinitisticDimension Λᵐᵒᵖ = 0 ∧
      ¬ InjectivesGenerate Λ ∧ InjectivesGenerate Λᵐᵒᵖ

end LittleFinitistic

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.LittleFinitistic.extreme_left_right_asymmetry_statement

end Problem

/- Formalization scope, from lean/docs/198.md: The little finitistic-dimension conjecture predicts that finitely generated modules of finite projective dimension over a fixed finite-dimensional algebra have bounded projective dimensions. The formalized counterexample is a finite-dimensional complex algebra with a finitely generated module of projective dimension at least $2m-2$ and still finite for every $m\ge1$. A separate formalized result gives a finite-dimensional complex algebra whose little and big finitistic dimensions are infinite on the left and zero on the right. Injectives fail to generate its unbounded derived category on the left and generate it on the right. -/
