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

- problem_id: InfiniteMatroid
- collection: openai-math
- question_id: openai-math:185
- source: openai-math
- source_locator: lean/ComparatorChallenges/InfiniteMatroid.lean#OAI.InfiniteMatroidCounterexample.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Disproves the unrestricted infinite matroid intersection and packing/covering conjectures in ZFC, using two self-dual partitional matroids on a countably infinite ground set. The same examples answer Joó’s partitional-matroid question negatively. They are neither finitary nor cofinitary, so Nash-Williams’ original finitary conjecture remains outside the result. ([Lean](lean/docs/185.md)) We construct in ZFC two self-dual partitional matroids on a countably infinite common ground set that admit neither a packing/covering partition nor an intersection witness. This disproves the unrestricted infinite matroid packing/covering and intersection conjectures and answers Joó's question for two partitional matroids negatively. The examples are neither finitary nor cofinitary.
- notes: OpenAI math result family 185, Counterexamples to infinite matroid intersection and packing/covering -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/185.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.InfiniteMatroidCounterexample.main
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.InfiniteMatroid.Main
- source_main_result: OAI.InfiniteMatroidCounterexample.main
- source_papers: preprints/A-Counterexample-to-the-Infinite-Matroid-Packing-Covering-Conjecture-September-24-2026/paper.pdf
- source_scope_note: lean/docs/185.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace InfiniteMatroidCounterexample
open Matroid

abbrev D := (m : ℕ) × ((Fin m → Bool) → Bool)
abbrev E := ℤ × D

def contractOnto {α : Type*} (M : Matroid α) (C : Set α) : Matroid α :=
  (M.dual ↾ C).dual

def HasPackingCovering {α : Type*} (M₀ M₁ : Matroid α) : Prop :=
  ∃ P C S₀ S₁ I₀ I₁ : Set α,
    Disjoint P C ∧ P ∪ C = M₀.E ∧ M₁.E = M₀.E ∧
    S₀ ⊆ P ∧ S₁ ⊆ P ∧ Disjoint S₀ S₁ ∧
    (M₀ ↾ P).Spanning S₀ ∧ (M₁ ↾ P).Spanning S₁ ∧
    I₀ ⊆ C ∧ I₁ ⊆ C ∧
    (contractOnto M₀ C).Indep I₀ ∧
    (contractOnto M₁ C).Indep I₁ ∧ I₀ ∪ I₁ = C

def main_statement : Prop :=
  Countable E ∧ Infinite E ∧
    ∃ M₀ M₁ : Matroid E,
      M₀.E = Set.univ ∧ M₁.E = Set.univ ∧
      M₀.dual = M₀ ∧ M₁.dual = M₁ ∧
      (∀ I₀ I₁ : Set E, M₀.Indep I₀ → M₁.Indep I₁ → I₀ ∪ I₁ ≠ Set.univ) ∧
      ¬ HasPackingCovering M₀ M₁

end InfiniteMatroidCounterexample

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.InfiniteMatroidCounterexample.main_statement

end Problem

/- Formalization scope, from lean/docs/185.md: The infinite matroid packing/covering conjecture predicts a partition of a common ground set into parts admitting the corresponding packing and covering. The formalization constructs two self-dual partitional matroids on one countably infinite ground set that admit neither an independent covering nor a packing/covering partition. The same pair has no intersection witness, so it also refutes the unrestricted infinite matroid intersection conjecture. Separate formalized consequences give counterexamples to the individual covering and packing conjectures. The construction is in ordinary set theory with Choice and assumes no finitary restriction on the matroids. -/
