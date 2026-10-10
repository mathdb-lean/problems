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

- problem_id: PlaneColoring
- collection: openai-math
- question_id: openai-math:158
- source: openai-math
- source_locator: lean/ComparatorChallenges/PlaneColoring.lean#OAI.Problem160.properColoring_seven
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that every five-coloring of the Euclidean plane has a monochromatic pair at distance one, with no restriction on the color classes. This advances the Hadwiger–Nelson problem: together with the classical seven-coloring, only six and seven remain possible chromatic numbers of the plane. ([Lean](lean/docs/158.md)) We prove that every coloring of the Euclidean plane with five colors has a monochromatic unit-distance pair, with no regularity assumption on the color classes. Consequently, the chromatic number of the plane is either six or seven.
- notes: OpenAI math result family 158, The Euclidean plane cannot be colored with five colors -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/158.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Problem160.properColoring_seven
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.PlaneColoring.Main
- source_main_result: OAI.Problem160.properColoring_seven
- source_papers: preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf
- source_scope_note: lean/docs/158.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

namespace Problem160

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def ProperColoring (k : ℕ) : Prop :=
  ∃ c : Plane → Fin k,
    ∀ x y : Plane, dist x y = 1 → c x ≠ c y

def properColoring_seven_statement : Prop :=
  ProperColoring 7

end Problem160

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Problem160.properColoring_seven_statement

end Problem

/- Formalization scope, from lean/docs/158.md: The Hadwiger–Nelson problem asks for the fewest colors needed to color the plane so that points at distance one have different colors. The formalized results prove that five colors do not suffice and that seven colors do suffice. The lower bound applies to arbitrary colorings, with no measurability or continuity assumption; the upper bound includes every boundary point of the coloring regions. -/
