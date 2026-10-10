import Mathlib.Topology.Path
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive
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

- problem_id: BipartiteCrossing
- collection: openai-math
- question_id: openai-math:165
- source: openai-math
- source_locator: lean/ComparatorChallenges/BipartiteCrossing.lean#OAI.Zarankiewicz.mainTarget_proof
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the Harary–Hill conjecture and Turán's brickyard problem in the Zarankiewicz formulation, determining the crossing numbers of every complete and complete bipartite graph. The result proves the optimality of the classical drawings among all plane drawings with continuous edge arcs. ([Lean](lean/docs/165.md)) We prove the Harary–Hill conjecture: for every positive integer n, the ordinary crossing number of the complete graph Kn is We prove the Zarankiewicz crossing-number conjecture, resolving Turán's brickyard problem. For all positive integers m, n, the ordinary crossing number of the complete bipartite graph $`K_{m,n}`$ is
- notes: OpenAI math result family 165, The Harary–Hill and Zarankiewicz crossing-number formulas -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/165.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Zarankiewicz.mainTarget_proof
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.Crossing.Main
- source_main_result: OAI.Zarankiewicz.mainTarget_proof
- source_papers: preprints/The-crossing-number-of-complete-graphs-September-23-2026/paper.pdf preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf
- source_scope_note: lean/docs/165.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

namespace Zarankiewicz

def axisPairs (r : ℕ) : ℕ := (r/2) * ((r-1)/2)


abbrev Plane := ℝ × ℝ
abbrev BipartiteVertex (m n : ℕ) := Fin m ⊕ Fin n
abbrev BipartiteEdge (m n : ℕ) := Fin m × Fin n

structure ContinuousDrawing (m n : ℕ) where
  vertex : BipartiteVertex m n → Plane
  vertex_injective : Function.Injective vertex
  edge : ∀ e : BipartiteEdge m n, Path (vertex (.inl e.1)) (vertex (.inr e.2))
  edge_injective : ∀ e, Function.Injective (edge e)
  interior_avoids_vertices : ∀ e t, t ∈ Set.Ioo (0 : unitInterval) 1 →
    ∀ v, edge e t ≠ vertex v

def edgeInterior {m n : ℕ} (D : ContinuousDrawing m n) (e : BipartiteEdge m n) : Set Plane :=
  D.edge e '' Set.Ioo (0 : unitInterval) 1

def ProperCrossing (A B : Set Plane) (x : Plane) : Prop :=
  ∃ chart : OpenPartialHomeomorph Plane Plane,
    x ∈ chart.source ∧ chart x = (0,0) ∧
    chart '' (chart.source ∩ A) = chart.target ∩ {y | y.2 = 0} ∧
    chart '' (chart.source ∩ B) = chart.target ∩ {y | y.1 = 0}

def crossingPoints {m n : ℕ} (D : ContinuousDrawing m n) : Set Plane :=
  {x | ∃ e f : BipartiteEdge m n, e ≠ f ∧ x ∈ edgeInterior D e ∧ x ∈ edgeInterior D f}

structure AdmissibleDrawing (m n : ℕ) extends ContinuousDrawing m n where
  crossings_finite : (crossingPoints toContinuousDrawing).Finite
  crossings_proper : ∀ e f, e ≠ f → ∀ x,
    x ∈ edgeInterior toContinuousDrawing e → x ∈ edgeInterior toContinuousDrawing f →
    ProperCrossing (edgeInterior toContinuousDrawing e) (edgeInterior toContinuousDrawing f) x
  no_triples : ∀ e f g, e ≠ f → e ≠ g → f ≠ g →
    edgeInterior toContinuousDrawing e ∩ edgeInterior toContinuousDrawing f ∩
      edgeInterior toContinuousDrawing g = ∅

def crossingCount {m n : ℕ} (D : AdmissibleDrawing m n) : ℕ := D.crossings_finite.toFinset.card

def MainTarget : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    (∃ D : AdmissibleDrawing m n, crossingCount D = axisPairs m * axisPairs n) ∧
    (∀ D : AdmissibleDrawing m n, axisPairs m * axisPairs n ≤ crossingCount D)

def mainTarget_proof_statement : Prop :=
  MainTarget

end Zarankiewicz

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Zarankiewicz.mainTarget_proof_statement

end Problem

/- Formalization scope, from lean/docs/165.md: The formalized result proves Hill's proposed formula for the crossing number of the complete graph: for every $n\ge3$, $\mathrm{cr}(K_n)=\frac14\lfloor n/2\rfloor\lfloor(n-1)/2\rfloor\lfloor(n-2)/2\rfloor\lfloor(n-3)/2\rfloor$. It proves the lower bound and constructs a matching two-page drawing. Crossings are spatial points, so repeated crossings of one edge pair count separately. Zarankiewicz's crossing-number conjecture predicts $\mathrm{cr}(K_{m,n})=\lfloor m/2\rfloor\lfloor(m-1)/2\rfloor\lfloor n/2\rfloor\lfloor(n-1)/2\rfloor$. The formalized result proves this equality for every positive $m,n$ and constructs a drawing attaining it. Crossings are counted as spatial points for continuous simple edge paths, including repeated crossings between the same pair of edges. -/
