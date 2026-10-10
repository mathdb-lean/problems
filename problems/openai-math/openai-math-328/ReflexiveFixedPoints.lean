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

- problem_id: ReflexiveFixedPoints
- collection: openai-math
- question_id: openai-math:328
- source: openai-math
- source_locator: lean/ComparatorChallenges/ReflexiveFixedPoints.lean#OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves Kirk's reflexive-space fixed-point problem: every nonexpansive selfmap of a nonempty closed bounded convex subset of a real reflexive Banach space has a fixed point. The result uses the original norm, without assuming uniform convexity. ([Lean](lean/docs/328.md)) Every nonexpansive selfmap of a nonempty closed bounded convex subset of a real reflexive Banach space has a fixed point. This resolves the reflexive-space fixed point problem for the given norm.
- notes: OpenAI math result family 328, Nonexpansive fixed points in reflexive Banach spaces -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/328.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.Nonexpansive.Main
- source_main_result: OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive
- source_papers: preprints/Fixed-Points-of-Nonexpansive-Maps-in-Reflexive-Banach-Spaces-September-24-2026/paper.pdf
- source_scope_note: lean/docs/328.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

namespace ReflexiveFixedPoints

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Surjectivity of the canonical map into the continuous bidual. -/
def CanonicallyReflexive : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)

variable {X}

/-- Every nonexpansive selfmap of a nonempty closed bounded convex set has
an actual fixed point, with nonexpansiveness stated in the original norm. -/
def exists_fixedPoint_of_canonicallyReflexive_statement : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (hX : CanonicallyReflexive X) (C : Set X) (hne : C.Nonempty) (hclosed : IsClosed C) (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C) (F : C → C) (hF : ∀ a b : C, ‖(F a : X) - (F b : X)‖ ≤ ‖(a : X) - (b : X)‖),
    ∃ a : C, F a = a

end ReflexiveFixedPoints

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive_statement.{u}

end Problem

/- Formalization scope, from lean/docs/328.md: The fixed-point question asks whether reflexivity suffices for nonexpansive maps on bounded convex sets. The formalized result gives an affirmative answer: every nonexpansive self-map of a nonempty closed bounded convex subset of a real reflexive Banach space has a fixed point in the original norm. Zero and nonseparable spaces are included, with no uniform convexity, normal structure, or weak-continuity assumption. -/
