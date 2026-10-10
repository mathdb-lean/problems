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

- problem_id: CycleDecomposition
- collection: openai-math
- question_id: openai-math:181
- source: openai-math
- source_locator: lean/ComparatorChallenges/CycleDecomposition.lean#OAI.ErdosGallai.erdos_gallai
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that the edges of every finite simple undirected graph on n vertices can be partitioned into at most $`Cn`$ simple cycles and single edges, for an absolute constant C. This resolves the Erdős–Gallai cycle-decomposition conjecture, bounding the number of pieces linearly even for dense graphs. ([Lean](lean/docs/181.md)) We prove that every finite simple undirected graph on n vertices has an edge partition into at most $`Cn`$ simple cycles and single edges, for an absolute constant C. This resolves the Erdős–Gallai cycle decomposition conjecture positively.
- notes: OpenAI math result family 181, The Erdős–Gallai cycle-decomposition conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/181.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ErdosGallai.erdos_gallai
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.CycleDecomposition.Main
- source_main_result: OAI.ErdosGallai.erdos_gallai
- source_papers: preprints/A-linear-cycle-and-edge-decomposition-of-every-graph-September-24-2026/main.pdf
- source_scope_note: lean/docs/181.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section


open Filter Asymptotics Real
open scoped Topology

open MeasureTheory ProbabilityTheory Finset

namespace ErdosGallai

def CycleOrSingleEdge {V : Type} (G : SimpleGraph V)
    (s : Set (Sym2 V)) : Prop :=
  (∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s = p.edgeSet) ∨
  ∃ e ∈ G.edgeSet, s = {e}

def EdgeDecomposition {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ parts : Fin k → Set (Sym2 V),
    (∀ i, CycleOrSingleEdge G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet


def MainStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ∃ k : ℕ, EdgeDecomposition G k ∧ (k : ℝ) ≤ C * n

def erdos_gallai_statement : Prop :=
  MainStatement

end ErdosGallai

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ErdosGallai.erdos_gallai_statement

end Problem

/- Formalization scope, from lean/docs/181.md: The Erdős–Gallai cycle-decomposition conjecture asks for a linear bound on the number of cycles and single edges needed to partition a graph's edges. The formalized result gives one absolute constant $C>0$ such that every finite simple graph on $n$ vertices has an edge-disjoint decomposition into at most $Cn$ cycles or singleton edges. Edgeless and small graphs are included. The optimal value of $C$ is not determined. -/
