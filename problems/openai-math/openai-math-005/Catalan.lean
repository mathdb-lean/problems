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

- problem_id: Catalan
- collection: openai-math
- question_id: openai-math:005
- source: openai-math
- source_locator: lean/ComparatorChallenges/Catalan.lean#OAI.InternalCatalan.catalan_irrational
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that Catalan's constant $`G=\sum_{j\ge0}(-1)^j/(2j+1)^2`$ is irrational. ([Lean](lean/docs/005.md)) We prove that Catalan's constant $`G=\sum_{j\geq0}(-1)^j/(2j+1)^2`$ is irrational.
- notes: OpenAI math result family 005, Irrationality of Catalan’s constant -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/005.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.InternalCatalan.catalan_irrational
- source_theorem_count: 1
- source_solution_module: OAI.NumberTheory.Catalan.Main
- source_papers: preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf
- source_scope_note: lean/docs/005.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace InternalCatalan

def catalan_irrational_statement : Prop :=
  Irrational (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)

end InternalCatalan

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.InternalCatalan.catalan_irrational_statement

end Problem

/- Formalization scope, from lean/docs/005.md: The formalization proves that Catalan's constant $G=\sum_{j=0}^{\infty}(-1)^j/(2j+1)^2$ is irrational. This is the mathematical assertion in the paper's title. -/
