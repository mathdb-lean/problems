import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.Path
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

- problem_id: CompleteCrossing
- collection: openai-math
- question_id: openai-math:165
- source: openai-math
- source_locator: lean/ComparatorChallenges/CompleteCrossing.lean#OAI.Paper170.complete_graph_crossing_number
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the Harary–Hill conjecture and Turán's brickyard problem in the Zarankiewicz formulation, determining the crossing numbers of every complete and complete bipartite graph. The result proves the optimality of the classical drawings among all plane drawings with continuous edge arcs. ([Lean](lean/docs/165.md)) We prove the Harary–Hill conjecture: for every positive integer n, the ordinary crossing number of the complete graph Kn is We prove the Zarankiewicz crossing-number conjecture, resolving Turán's brickyard problem. For all positive integers m, n, the ordinary crossing number of the complete bipartite graph $`K_{m,n}`$ is
- notes: OpenAI math result family 165, The Harary–Hill and Zarankiewicz crossing-number formulas -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/165.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Paper170.complete_graph_crossing_number
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.CompleteCrossing.Main
- source_main_result: OAI.Paper170.complete_graph_crossing_number
- source_papers: preprints/The-crossing-number-of-complete-graphs-September-23-2026/paper.pdf preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf
- source_scope_note: lean/docs/165.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

namespace Paper170

abbrev Plane := ℝ × ℝ

structure Graph (Vertex Edge : Type) where
  src : Edge → Vertex
  dst : Edge → Vertex
  loopless : ∀ edge, src edge ≠ dst edge
  simple : ∀ edge other, ((src edge = src other ∧ dst edge = dst other) ∨
    (src edge = dst other ∧ dst edge = src other)) → edge = other

abbrev CompleteEdge (order : ℕ) := {pair : Fin order × Fin order // pair.1 < pair.2}

def completeGraph (order : ℕ) : Graph (Fin order) (CompleteEdge order) where
  src edge := edge.val.1
  dst edge := edge.val.2
  loopless edge := ne_of_lt edge.property
  simple edge other same := by
    rcases same with same | reversed
    · exact Subtype.ext (Prod.ext same.1 same.2)
    · have increasing := edge.property
      have other_increasing := other.property
      rw [reversed.1, reversed.2] at increasing
      exact (lt_asymm increasing other_increasing).elim

variable {Vertex Edge : Type}

structure ContinuousDrawing (graph : Graph Vertex Edge) where
  vertex : Vertex → Plane
  vertex_injective : Function.Injective vertex
  edge : ∀ edge : Edge, Path (vertex (graph.src edge)) (vertex (graph.dst edge))
  edge_injective : ∀ selected, Function.Injective (edge selected)
  interior_avoids_vertices : ∀ selected time, time ∈ Set.Ioo (0 : unitInterval) 1 →
    ∀ other, edge selected time ≠ vertex other

variable {graph : Graph Vertex Edge}

def edgeInterior (drawing : ContinuousDrawing graph) (edge : Edge) : Set Plane :=
  drawing.edge edge '' Set.Ioo (0 : unitInterval) 1

structure ProperCrossing (first second : Set Plane) (point : Plane) : Prop where
  chart_exists : ∃ chart : OpenPartialHomeomorph Plane Plane,
    point ∈ chart.source ∧ chart point = (0, 0) ∧
    chart '' (chart.source ∩ first) = chart.target ∩ {image | image.2 = 0} ∧
    chart '' (chart.source ∩ second) = chart.target ∩ {image | image.1 = 0}

def crossingPoints (drawing : ContinuousDrawing graph) : Set Plane :=
  {point | ∃ edge other : Edge, edge ≠ other ∧
    point ∈ edgeInterior drawing edge ∧ point ∈ edgeInterior drawing other}

structure AdmissibleDrawing (graph : Graph Vertex Edge) extends ContinuousDrawing graph where
  crossings_finite : (crossingPoints toContinuousDrawing).Finite
  crossings_proper : ∀ edge other, edge ≠ other → ∀ point,
    point ∈ edgeInterior toContinuousDrawing edge →
    point ∈ edgeInterior toContinuousDrawing other →
    ProperCrossing (edgeInterior toContinuousDrawing edge)
      (edgeInterior toContinuousDrawing other) point
  no_triples : ∀ first second third, first ≠ second → first ≠ third → second ≠ third →
    edgeInterior toContinuousDrawing first ∩ edgeInterior toContinuousDrawing second ∩
      edgeInterior toContinuousDrawing third = ∅

def crossingCount (drawing : AdmissibleDrawing graph) : ℕ :=
  drawing.crossings_finite.toFinset.card

def ordinaryCrossingNumber (graph : Graph Vertex Edge) : ℕ :=
  sInf (Set.range (@crossingCount Vertex Edge graph))

def hill (order : ℕ) : ℕ :=
  (order / 2 * ((order - 1) / 2) * ((order - 2) / 2) * ((order - 3) / 2)) / 4

def complete_graph_crossing_number_statement : Prop :=
  ∀ (order : ℕ) (at_least_three : 3 ≤ order),
    ordinaryCrossingNumber (completeGraph order) = hill order

end Paper170

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Paper170.complete_graph_crossing_number_statement

end Problem

/- Formalization scope, from lean/docs/165.md: The formalized result proves Hill's proposed formula for the crossing number of the complete graph: for every $n\ge3$, $\mathrm{cr}(K_n)=\frac14\lfloor n/2\rfloor\lfloor(n-1)/2\rfloor\lfloor(n-2)/2\rfloor\lfloor(n-3)/2\rfloor$. It proves the lower bound and constructs a matching two-page drawing. Crossings are spatial points, so repeated crossings of one edge pair count separately. Zarankiewicz's crossing-number conjecture predicts $\mathrm{cr}(K_{m,n})=\lfloor m/2\rfloor\lfloor(m-1)/2\rfloor\lfloor n/2\rfloor\lfloor(n-1)/2\rfloor$. The formalized result proves this equality for every positive $m,n$ and constructs a drawing attaining it. Crossings are counted as spatial points for continuous simple edge paths, including repeated crossings between the same pair of edges. -/
