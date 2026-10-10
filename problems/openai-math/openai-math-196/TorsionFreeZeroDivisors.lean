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

- problem_id: TorsionFreeZeroDivisors
- collection: openai-math
- question_id: openai-math:196
- source: openai-math
- source_locator: lean/ComparatorChallenges/TorsionFreeZeroDivisors.lean#OAI.TorsionFreeZeroDivisors.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a finitely presented torsion-free group G whose group algebra $`\mathbb F_2[G]`$ has nonzero zero divisors, disproving Kaplansky's zero-divisor conjecture. The group has a finite two-dimensional classifying space. ([Lean](lean/docs/196.md)) We disprove Kaplansky's zero-divisor conjecture by constructing a finitely presented torsion-free group G for which $`\mathbb F_2[G]`$ has nonzero zero divisors. The group admits a finite two-dimensional classifying space.
- notes: OpenAI math result family 196, A counterexample to Kaplansky’s zero-divisor conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/196.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.TorsionFreeZeroDivisors.main
- source_theorem_count: 1
- source_solution_module: OAI.Algebra.GroupRing.Main
- source_main_result: OAI.TorsionFreeZeroDivisors.main
- source_papers: preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf
- source_scope_note: lean/docs/196.md
- source_field: Algebra
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace TorsionFreeZeroDivisors

/-- Ordinary group torsion-freeness, without requiring uniqueness of all roots. -/
def TorsionFree (G : Type) [Group G] : Prop :=
  ∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1

/-- A connected finite Hausdorff 2-dimensional CW K(G,1). -/
def HasFiniteTwoDimensionalClassifyingSpace (G : Type) [Group G] : Prop :=
  ∃ (X : Type) (topX : TopologicalSpace X),
    letI : TopologicalSpace X := topX
    ∃ (_hausdorff : T2Space X) (_connected : PathConnectedSpace X)
      (cw : Topology.CWComplex (Set.univ : Set X)),
      letI : Topology.CWComplex (Set.univ : Set X) := cw
      Topology.CWComplex.Finite (Set.univ : Set X) ∧
      (∀ n : ℕ, 2 < n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n)) ∧
      Nonempty (Topology.CWComplex.cell (Set.univ : Set X) 2) ∧
      ∃ (x : X), Nonempty (G ≃* FundamentalGroup X x) ∧
        ∃ (E : Type) (topE : TopologicalSpace E),
          letI : TopologicalSpace E := topE
          ContractibleSpace E ∧
          ∃ p : E → X, IsCoveringMap p ∧ Function.Surjective p

/-- The entire main theorem, including its "Moreover" clause. -/
def MainTheorem : Prop :=
  ∃ (G : Type) (inst : Group G),
    letI : Group G := inst
    Group.IsFinitelyPresented G ∧ TorsionFree G ∧
    HasFiniteTwoDimensionalClassifyingSpace G ∧
    ∃ α β : MonoidAlgebra (ZMod 2) G, α ≠ 0 ∧ β ≠ 0 ∧ α * β = 0

def main_statement : Prop :=
  MainTheorem

end TorsionFreeZeroDivisors

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.TorsionFreeZeroDivisors.main_statement

end Problem

/- Formalization scope, from lean/docs/196.md: Kaplansky's zero-divisor conjecture asserts that the group algebra of a torsion-free group over a field has no zero divisors. The formalized result constructs a finitely presented torsion-free group $G$ and nonzero elements $\alpha,\beta\in\mathbb F_2[G]$ with $\alpha\beta=0$, giving a counterexample. The same group admits a finite two-dimensional classifying space $K(G,1)$. -/
