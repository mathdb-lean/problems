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

- problem_id: EilenbergGanea
- collection: openai-math
- question_id: openai-math:249
- source: openai-math
- source_locator: lean/ComparatorChallenges/EilenbergGanea.lean#OAI.EilenbergGanea.source_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a finitely generated residually finite group with integral cohomological dimension two and geometric dimension three, disproving the Eilenberg–Ganea conjecture. It has no two-dimensional classifying space, even with infinitely many cells. ([Lean](lean/docs/249.md)) We construct a finitely generated residually finite group of integral cohomological dimension two and geometric dimension three, disproving the Eilenberg–Ganea conjecture.
- notes: OpenAI math result family 249, A finitely generated Eilenberg–Ganea counterexample -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/249.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.EilenbergGanea.source_main
- source_theorem_count: 1
- source_solution_module: OAI.Topology.EilenbergGanea.Main
- source_papers: preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf
- source_scope_note: lean/docs/249.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open Classical Set Topology

namespace EilenbergGanea

/-- The signed words encode the relators `x²y⁻⁵` and `x²(yx⁻¹)³`. -/
def seedWord : Bool → List (Bool × Bool)
  | false => [(false, true), (false, true), (true, false), (true, false),
      (true, false), (true, false), (true, false)]
  | true => [(false, true), (false, true), (true, true), (false, false),
      (true, true), (false, false), (true, true), (false, false)]

def boundaryLength (relation : Bool) : ℕ := 3 * (seedWord relation).length

abbrev RoseVertex := Option (Bool × Fin 2)
abbrev SeedVertex := RoseVertex ⊕ Bool
abbrev CircleEdge := Bool × Fin 3
abbrev Sector := (relation : Bool) × Fin (boundaryLength relation)
abbrev SeedEdge := CircleEdge ⊕ Sector
abbrev SeedCell := SeedVertex ⊕ (SeedEdge ⊕ Sector)

def circleStart (edge : CircleEdge) : RoseVertex :=
  ![none, some (edge.1, 0), some (edge.1, 1)] edge.2

def circleEnd (edge : CircleEdge) : RoseVertex :=
  ![some (edge.1, 0), some (edge.1, 1), none] edge.2

def sectorLetter (sector : Sector) : Bool × Bool :=
  (seedWord sector.1).get ⟨sector.2.val / 3, by
    have bound := sector.2.isLt
    dsimp [boundaryLength] at bound
    omega⟩

def sectorCircleEdge (sector : Sector) : CircleEdge :=
  ((sectorLetter sector).1, if (sectorLetter sector).2 then
    ⟨sector.2.val % 3, Nat.mod_lt _ (by decide)⟩ else
    ⟨2 - sector.2.val % 3, by omega⟩)

def sectorStart (sector : Sector) : RoseVertex :=
  if (sectorLetter sector).2 then circleStart (sectorCircleEdge sector)
  else circleEnd (sectorCircleEdge sector)

def nextSector (sector : Sector) : Sector :=
  ⟨sector.1, ⟨(sector.2.val + 1) % boundaryLength sector.1,
    Nat.mod_lt _ (by have := sector.2.isLt; omega)⟩⟩

def edgeVertices : SeedEdge → Finset SeedVertex
  | .inl edge => {.inl (circleStart edge), .inl (circleEnd edge)}
  | .inr sector => {.inr sector.1, .inl (sectorStart sector)}

def sectorEdges (sector : Sector) : Finset SeedEdge :=
  {.inl (sectorCircleEdge sector), .inr sector, .inr (nextSector sector)}

def sectorVertices (sector : Sector) : Finset SeedVertex :=
  (sectorEdges sector).biUnion edgeVertices

def properFace : SeedCell → SeedCell → Prop
  | .inl vertex, .inr (.inl edge) => vertex ∈ edgeVertices edge
  | .inl vertex, .inr (.inr sector) => vertex ∈ sectorVertices sector
  | .inr (.inl edge), .inr (.inr sector) => edge ∈ sectorEdges sector
  | _, _ => False

/-- Comparability graph of the seven vertices, 51 edges and 45 sectors. -/
def seedGraph : SimpleGraph SeedCell where
  Adj first second := properFace first second ∨ properFace second first
  symm := ⟨fun _ _ adjacent => adjacent.elim Or.inr Or.inl⟩
  loopless := ⟨by
    intro cell
    rcases cell with vertex | cell
    · simp [properFace]
    · rcases cell with edge | sector <;> simp [properFace]⟩

def artinRelations {Vertex : Type*} (graph : SimpleGraph Vertex) : Set (FreeGroup Vertex) :=
  {word | ∃ first second, graph.Adj first second ∧
    word = FreeGroup.of first * FreeGroup.of second *
      (FreeGroup.of first)⁻¹ * (FreeGroup.of second)⁻¹}

abbrev ArtinGroup {Vertex : Type*} (graph : SimpleGraph Vertex) :=
  PresentedGroup (artinRelations graph)

def height {Vertex : Type*} (graph : SimpleGraph Vertex) :
    ArtinGroup graph →* Multiplicative ℤ :=
  PresentedGroup.toGroup (f := fun _ : Vertex => Multiplicative.ofAdd (1 : ℤ)) (by
    rintro word ⟨first, second, _, rfl⟩
    simp)

abbrev SourceGroup := (height seedGraph).ker

/-- Projective dimension of the trivial integral left group-ring module. -/
def cohomologicalDimension (GroupType : Type*) [Group GroupType] : WithBot ℕ∞ :=
  CategoryTheory.projectiveDimension
    (ModuleCat.of (MonoidAlgebra ℤ GroupType)
      (Representation.trivial ℤ GroupType ℤ).asModule)

universe u

/-- Ordinary classifying CW spaces, with no bound on the cardinality of their cells. -/
def HasClassifyingSpace (GroupType : Type*) [Group GroupType] (dimension : ℕ) : Prop :=
  ∃ (Space : Type u) (_ : TopologicalSpace Space) (_ : T2Space Space)
    (_ : Topology.CWComplex (Set.univ : Set Space)),
    (∀ degree : ℕ, dimension < degree →
      IsEmpty (Topology.CWComplex.cell (Set.univ : Set Space) degree)) ∧
    PathConnectedSpace Space ∧
    ∃ basepoint : Space, Nonempty (FundamentalGroup Space basepoint ≃* GroupType) ∧
    ∃ (Cover : Type u) (_ : TopologicalSpace Cover), ContractibleSpace Cover ∧
    ∃ projection : Cover → Space, IsCoveringMap projection ∧ Function.Surjective projection

def source_main_statement : Prop :=
  Group.FG SourceGroup ∧ Group.ResiduallyFinite SourceGroup ∧
    cohomologicalDimension SourceGroup = 2 ∧
    HasClassifyingSpace.{0} SourceGroup 3 ∧
    ¬ HasClassifyingSpace.{u} SourceGroup 2

end EilenbergGanea

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.EilenbergGanea.source_main_statement.{u}

end Problem

/- Formalization scope, from lean/docs/249.md: The Eilenberg–Ganea conjecture predicts that a group of integral cohomological dimension two has a two-dimensional classifying space. The formalization constructs a finitely generated residually finite group of cohomological dimension two that has a three-dimensional classifying space but no two-dimensional one. Thus its geometric dimension is three, contradicting the conjecture. -/
