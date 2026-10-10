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

- problem_id: FalconerAllDimensions
- collection: openai-math
- question_id: openai-math:073
- source: openai-math
- source_locator: lean/ComparatorChallenges/FalconerAllDimensions.lean#OAI.Falconer.falconer_distance_conjecture
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the Falconer distance conjecture in every dimension d ≥ 2: every compact set $`E\subset\mathbb R^d`$ with Hausdorff dimension greater than $`d/2`$ determines a set of Euclidean distances of positive Lebesgue measure. ([Lean](lean/docs/073.md)) We resolve the Falconer distance conjecture in every dimension. For every integer d ≥ 2, a compact subset of ℝd with Hausdorff dimension greater than $`d/2`$ determines a set of Euclidean distances of positive Lebesgue measure.
- notes: OpenAI math result family 073, The Falconer distance conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/073.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Falconer.falconer_distance_conjecture
- source_theorem_count: 1
- source_solution_module: OAI.MeasureTheory.Falconer.Campaign123PlanarFurstenbergProof
- source_papers: preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf
- source_scope_note: lean/docs/073.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace Falconer
open MeasureTheory
open scoped ENNReal

/-- A compact subset of Euclidean space with Hausdorff dimension greater than
half the ambient dimension determines a distance set of positive Lebesgue measure. -/
def falconer_distance_conjecture_statement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E →
      (d : ℝ≥0∞) / 2 < dimH E →
        0 < volume {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}

end Falconer

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Falconer.falconer_distance_conjecture_statement

end Problem

/- Formalization scope, from lean/docs/073.md: The formalization proves the Falconer distance conjecture in every dimension. For every integer $d\ge2$ and compact set $E\subset\mathbb R^d$ with Hausdorff dimension greater than $d/2$, the set $\{\lVert x-y\rVert:x,y\in E\}$ has positive Lebesgue measure. The linked statements include both this all-dimensional result and the earlier planar case. -/
