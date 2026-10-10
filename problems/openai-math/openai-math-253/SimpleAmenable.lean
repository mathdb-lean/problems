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

- problem_id: SimpleAmenable
- collection: openai-math
- question_id: openai-math:253
- source: openai-math
- source_locator: lean/ComparatorChallenges/SimpleAmenable.lean#OAI.SimpleAmenable.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs an infinite finitely presented simple amenable group, answering the longstanding question of whether these properties can occur simultaneously. ([Lean](lean/docs/253.md)) We construct an infinite finitely presented simple amenable group, giving a positive answer to the finite-presentation existence question for simple amenable groups.
- notes: OpenAI math result family 253, An infinite finitely presented simple amenable group -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/253.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SimpleAmenable.main
- source_theorem_count: 1
- source_solution_module: OAI.GroupTheory.SimpleAmenable.Main
- source_main_result: OAI.SimpleAmenable.main
- source_papers: preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf
- source_scope_note: lean/docs/253.md
- source_field: GroupTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open scoped symmDiff

namespace SimpleAmenable

noncomputable def FolnerAmenable (G : Type*) [Group G] : Prop := by
  classical
  exact ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
    ∃ D : Finset G, D.Nonempty ∧ ∀ g ∈ K,
      (((D.image (fun d => g * d)) ∆ D).card : ℝ) < ε * D.card

def main_statement : Prop :=
  ∃ (G : Type) (_ : Group G),
    Infinite G ∧ Group.IsFinitelyPresented G ∧ IsSimpleGroup G ∧ FolnerAmenable G

end SimpleAmenable

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SimpleAmenable.main_statement

end Problem

/- Formalization scope, from lean/docs/253.md: The formalized result answers the existence question affirmatively: there is one group that is infinite, finitely presented, simple, and amenable. Amenability is expressed by the Følner condition. The later general claims about central kernels and enlargements across families are not included. -/
