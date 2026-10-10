import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Union
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

- problem_id: SeymourSecondNeighborhood
- collection: openai-math
- question_id: openai-math:173
- source: openai-math
- source_locator: lean/ComparatorChallenges/SeymourSecondNeighborhood.lean#OAI.SeymourSecondNeighborhood.exists_goodVertex
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Seymour's second-neighborhood conjecture: every nonempty finite oriented graph has a vertex with at least as many vertices at directed distance exactly two as at directed distance one. Oriented graphs may be arbitrary apart from the exclusion of loops and oppositely directed edge pairs. ([Lean](lean/docs/173.md)) We prove that every nonempty finite oriented graph has a vertex with at least as many vertices at directed distance two as at directed distance one. This resolves Seymour's second neighborhood conjecture positively.
- notes: OpenAI math result family 173, Seymour’s second-neighborhood conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/173.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SeymourSecondNeighborhood.exists_goodVertex
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.SecondNeighborhood.Main
- source_main_result: OAI.SeymourSecondNeighborhood.exists_goodVertex
- source_papers: preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf
- source_scope_note: lean/docs/173.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*}

structure IsOriented (r : V → V → Prop) : Prop where
  loopless : ∀ v, ¬ r v v
  asymmetric : ∀ {u v}, r u v → ¬ r v u

variable [Fintype V] [DecidableEq V]

noncomputable section

def firstNeighbors (r : V → V → Prop) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (r v)

def secondNeighbors (r : V → V → Prop) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w =>
    w ≠ v ∧ ¬ r v w ∧ ∃ u, r v u ∧ r u w)

def GoodVertex (r : V → V → Prop) (v : V) : Prop :=
  (firstNeighbors r v).card ≤ (secondNeighbors r v).card

end

variable [Nonempty V]

def exists_goodVertex_statement : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (r : V → V → Prop) (hr : IsOriented r),
    ∃ v, GoodVertex r v

end SeymourSecondNeighborhood

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1} : Prop :=
  _root_.OAI.SeymourSecondNeighborhood.exists_goodVertex_statement.{u_1}

end Problem

/- Formalization scope, from lean/docs/173.md: Seymour's second-neighborhood conjecture asserts that every nonempty finite oriented graph has a vertex with at least as many second out-neighbors as first out-neighbors. The formalized result proves this assertion, where the second neighborhood consists of vertices at directed distance exactly two. The initial vertex and first neighbors are excluded from that count, and sinks are included. -/
