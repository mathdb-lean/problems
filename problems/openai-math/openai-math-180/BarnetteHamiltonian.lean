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

- problem_id: BarnetteHamiltonian
- collection: openai-math
- question_id: openai-math:180
- source: openai-math
- source_locator: lean/ComparatorChallenges/BarnetteHamiltonian.lean#OAI.Barnette.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that every finite simple cubic bipartite planar 3-vertex-connected graph has a Hamiltonian cycle, resolving Barnette's conjecture. Equivalently, every three-edge path in a finite simple cubic 3-vertex-connected bipartite Pfaffian graph lies in a Hamiltonian cycle. ([Lean](lean/docs/180.md)) We prove Barnette's conjecture: every finite simple cubic bipartite planar 3-vertex-connected graph has a Hamiltonian cycle.
- notes: OpenAI math result family 180, Barnette’s Hamiltonian-cycle conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/180.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Barnette.main
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.Hamiltonian.Main
- source_papers: preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/paper.pdf
- source_scope_note: lean/docs/180.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace Barnette

universe u

/-- A topological plane drawing of a simple graph, with no crossings. -/
structure PlaneEmbedding {V : Type u} (G : SimpleGraph V) where
  point : V → ℝ × ℝ
  point_injective : Function.Injective point
  arc : ∀ (v w : V), G.Adj v w → Path (point v) (point w)
  arc_injective : ∀ (v w : V) (h : G.Adj v w),
    Function.Injective (arc v w h)
  arc_reverse : ∀ (v w : V) (h : G.Adj v w),
    arc w v h.symm = (arc v w h).symm
  arc_avoids_vertices : ∀ (v w : V) (h : G.Adj v w)
    (t : unitInterval) (z : V),
    arc v w h t = point z →
      (t = 0 ∧ z = v) ∨ (t = 1 ∧ z = w)
  interiors_disjoint : ∀ (v w x y : V) (h : G.Adj v w) (k : G.Adj x y)
    (t s : unitInterval),
    t ≠ 0 → t ≠ 1 → s ≠ 0 → s ≠ 1 →
    arc v w h t = arc x y k s →
      (v = x ∧ w = y) ∨ (v = y ∧ w = x)

/-- Planarity means existence of a crossing-free topological plane embedding. -/
def Planar {V : Type u} (G : SimpleGraph V) : Prop :=
  Nonempty (PlaneEmbedding G)

/-- Deleting any set of at most two vertices leaves a connected graph of order at least two. -/
def ThreeVertexConnected {V : Type u} [Fintype V] (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card ≤ 2 → (G.induce {v | v ∉ S}).Connected

/-- A single spanning cycle, not a possibly disconnected spanning 2-factor. -/
def HasHamiltonianCycle {V : Type u} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ v : V, ∃ p : G.Walk v v, p.IsHamiltonianCycle

/-- Cubic bipartite three-vertex-connected plane graphs have a Hamiltonian cycle. -/
def MainStatement : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj],
    G.IsRegularOfDegree 3 → G.IsBipartite → Planar G →
      ThreeVertexConnected G → HasHamiltonianCycle G

def main_statement : Prop :=
  MainStatement.{u}

end Barnette

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.Barnette.main_statement.{u}

end Problem

/- Formalization scope, from lean/docs/180.md: Barnette's conjecture states that every finite simple cubic bipartite planar graph that is 3-vertex-connected has a Hamiltonian cycle. The formalization proves this statement for every such graph. The selected result is the existence of a cycle visiting every vertex exactly once. -/
