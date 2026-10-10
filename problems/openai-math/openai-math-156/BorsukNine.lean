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

- problem_id: BorsukNine
- collection: openai-math
- question_id: openai-math:156
- source: openai-math
- source_locator: lean/ComparatorChallenges/BorsukNine.lean#OAI.BorsukNine.main_theorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a compact subset of ℝ9 that cannot be covered by ten sets of strictly smaller diameter, disproving Borsuk's covering assertion already in dimension nine. The example consists of rank-one orthogonal projectors onto lines in ℝ4, with the Frobenius metric. ([Lean](lean/docs/156.md)) The compact set of rank-one orthogonal projectors on ℝ4, with the Frobenius metric, cannot be covered by ten sets of strictly smaller diameter. It therefore gives a counterexample to Borsuk's conjecture in dimension nine.
- notes: OpenAI math result family 156, Borsuk's conjecture fails in dimension nine -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/156.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.BorsukNine.main_theorem
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.Borsuk.Main
- source_main_result: OAI.BorsukNine.main_theorem
- source_papers: preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf
- source_scope_note: lean/docs/156.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace BorsukNine

abbrev Vector4 := EuclideanSpace ℝ (Fin 4)
abbrev Matrix4 := EuclideanSpace ℝ (Fin 4 × Fin 4)

def projector (u : Vector4) : Matrix4 :=
  WithLp.toLp 2 (fun ij => u ij.1 * u ij.2)

def projectorSet : Set Matrix4 :=
  projector '' {u : Vector4 | ‖u‖ = 1}

def traceOneSymmetric : Set Matrix4 :=
  {A | (∀ i j : Fin 4, A (i, j) = A (j, i)) ∧ ∑ i : Fin 4, A (i, i) = 1}

def HasTenSmallCover : Prop :=
  ∃ C : Fin 10 → Set Matrix4,
    (∀ i, C i ⊆ projectorSet) ∧
    projectorSet ⊆ ⋃ i, C i ∧
    ∀ i, Metric.diam (C i) < Real.sqrt 2

def main_theorem_statement : Prop :=
  IsCompact projectorSet ∧
    projectorSet ⊆ traceOneSymmetric ∧
    Metric.diam projectorSet = Real.sqrt 2 ∧
    ¬ HasTenSmallCover

end BorsukNine

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.BorsukNine.main_theorem_statement

end Problem

/- Formalization scope, from lean/docs/156.md: Borsuk's conjecture predicts that every bounded subset of $\mathbb R^d$ can be covered by $d+1$ sets of strictly smaller diameter. The formalized counterexample is the compact set of rank-one orthogonal projectors onto lines in $\mathbb R^4$, with the Frobenius metric. It lies in the nine-dimensional affine space of trace-one symmetric matrices, has diameter $\sqrt2$, and cannot be covered by ten arbitrary sets of smaller diameter. -/
