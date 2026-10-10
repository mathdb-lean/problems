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

- problem_id: SeparableQuotientNegative
- collection: openai-math
- question_id: openai-math:323
- source: openai-math
- source_locator: lean/ComparatorChallenges/SeparableQuotientNegative.lean#OAI.SeparableQuotient.negative_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Establishes, relative to the consistency of a measurable cardinal, that the separable quotient problem is independent of ZFC. The assertion that every infinite-dimensional Banach space has a separable infinite-dimensional quotient can hold for all real and complex Banach spaces, whereas the continuum hypothesis yields counterexamples over both fields. ([Lean](lean/docs/323.md)) The separable quotient problem asks whether every infinite-dimensional Banach space has a separable infinite-dimensional quotient. We prove that this statement is independent of ZFC, relative to the consistency of ZFC with a measurable cardinal. This holds over both the real and complex fields. For spaces of norm density ℵ1, we obtain independence relative to the consistency of ZFC alone.
- notes: OpenAI math result family 323, Independence of the separable quotient problem -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/323.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SeparableQuotient.negative_main
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.SeparableQuotients.Main
- source_papers: preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/paper.pdf
- source_scope_note: lean/docs/323.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace SeparableQuotient

open MeasureTheory Cardinal

universe u

/-- The continuum hypothesis. -/
def CH : Prop := Cardinal.mk ℝ = Cardinal.aleph 1

/-- A bounded linear surjection onto an infinite-dimensional separable Banach space. -/
def HasSeparableQuotient (𝕜 : Type) [RCLike 𝕜]
    (X : Type u) [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  ∃ (Y : Type u) (_ : NormedAddCommGroup Y) (_ : NormedSpace 𝕜 Y),
    CompleteSpace Y ∧ TopologicalSpace.SeparableSpace Y ∧
      (¬ FiniteDimensional 𝕜 Y) ∧ ∃ T : X →L[𝕜] Y, Function.Surjective T

/-- The separable quotient assertion at an arbitrary ambient universe. -/
def SQ (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    (¬ FiniteDimensional 𝕜 X) → HasSeparableQuotient 𝕜 X

def negative_main_statement : Prop :=
  ∀ (hCH : CH),
    ¬ SQ.{u} ℝ ∧ ¬ SQ.{u} ℂ

end SeparableQuotient

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.SeparableQuotient.negative_main_statement.{u}

end Problem

/- Formalization scope, from lean/docs/323.md: The separable quotient problem asks whether every infinite-dimensional Banach space has an infinite-dimensional separable quotient. The linked formalization proves the negative direction under the continuum hypothesis: over both the real and complex fields, there is an infinite-dimensional Banach space admitting no bounded linear surjection onto an infinite-dimensional separable Banach space. This is the conditional counterexample direction. The positive consistency direction and the paper's full relative-independence conclusions are outside the selected statement. -/
