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

- problem_id: PeriodicTilingThree
- collection: openai-math
- question_id: openai-math:155
- source: openai-math
- source_locator: lean/ComparatorChallenges/PeriodicTilingThree.lean#OAI.PeriodicTilingThree.periodic_tiling_counterexample_and_minimality
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a finite translational tile in ℤ3 that tiles space but admits no fully periodic tiling, disproving the periodic tiling conjecture in the smallest possible lattice dimension. Its unit-cube thickening gives the same counterexample in ℝ3, even with arbitrary real translation vectors. ([Lean](lean/docs/155.md)) We construct a finite translational tile in ℤ3 that admits tilings but no fully periodic tiling. Its unit-cube thickening has the same property in ℝ3, even when arbitrary real translations are allowed. This gives a negative resolution of the periodic tiling conjecture in dimension three.
- notes: OpenAI math result family 155, A counterexample to periodic tiling in dimension three -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/155.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.PeriodicTilingThree.periodic_tiling_counterexample_and_minimality
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.PeriodicTiling.Main
- source_main_result: OAI.PeriodicTilingThree.periodic_tiling_counterexample_and_minimality
- source_papers: preprints/A-translational-tile-with-no-fully-periodic-tiling-in-dimension-three-September-23-2026/paper.pdf
- source_scope_note: lean/docs/155.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

universe u

namespace PeriodicTilingThree

abbrev Lattice (d : ℕ) := Fin d → ℤ

variable {G : Type u} [AddCommGroup G]

def Tiles (F : Finset G) (A : Set G) : Prop :=
  Function.Bijective (fun p : ↥F × A => (p.1 : G) + (p.2 : G))

def Period (A : Set G) (v : G) : Prop :=
  ∀ x : G, x + v ∈ A ↔ x ∈ A

def FullyPeriodic (A : Set G) : Prop :=
  ∃ P : AddSubgroup G, P.FiniteIndex ∧ ∀ v ∈ P, Period A v

open MeasureTheory

abbrev Space (d : ℕ) := Fin d → ℝ

def castLattice {d : ℕ} : Lattice d →+ Space d where
  toFun z i := (z i : ℝ)
  map_zero' := by ext i; simp
  map_add' z w := by ext i; simp

def unitCube (d : ℕ) : Set (Space d) := Set.Icc 0 1

def Thickening {d : ℕ} (F : Finset (Lattice d)) : Set (Space d) :=
  {x | ∃ z ∈ F, x - castLattice z ∈ unitCube d}

def AETiles {d : ℕ} (Ω A : Set (Space d)) : Prop :=
  ∀ᵐ x ∂volume, ∃! a : A, x - (a : Space d) ∈ Ω

def latticeOfBasis {d : ℕ} (b : Module.Basis (Fin d) ℝ (Space d)) :
    AddSubgroup (Space d) := (Submodule.span ℤ (Set.range b)).toAddSubgroup

def EuclideanFullyPeriodic {d : ℕ} (A : Set (Space d)) : Prop :=
  ∃ b : Module.Basis (Fin d) ℝ (Space d), ∀ v ∈ latticeOfBasis b, Period A v

def HasTileWithoutPeriodicComplement (d : ℕ) : Prop :=
  ∃ T : Finset (Lattice d), T.Nonempty ∧
    (∃ A : Set (Lattice d), Tiles T A) ∧
    ∀ A : Set (Lattice d), Tiles T A → ¬ FullyPeriodic A

def periodic_tiling_counterexample_and_minimality_statement : Prop :=
  (∃ T : Finset (Lattice 3), T.Nonempty ∧
      (∃ A : Set (Lattice 3), Tiles T A) ∧
      (∀ A : Set (Lattice 3), Tiles T A → ¬ FullyPeriodic A) ∧
      (∃ A : Set (Space 3), AETiles (Thickening T) A) ∧
      (∀ A : Set (Space 3),
        AETiles (Thickening T) A → ¬ EuclideanFullyPeriodic A)) ∧
    IsLeast {d : ℕ | HasTileWithoutPeriodicComplement d} 3

end PeriodicTilingThree

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.PeriodicTilingThree.periodic_tiling_counterexample_and_minimality_statement

end Problem

/- Formalization scope, from lean/docs/155.md: The periodic-tiling question asks whether a finite tile that tiles a lattice must admit a periodic tiling. The formalized counterexample is a finite tile in $\mathbb Z^3$ that tiles but has no complement invariant under a finite-index subgroup. Its unit-cube thickening also tiles $\mathbb R^3$ almost everywhere but admits no fully periodic tiling, even with arbitrary real translation vectors. The result also establishes that dimension three is the least lattice dimension where this failure occurs. -/
