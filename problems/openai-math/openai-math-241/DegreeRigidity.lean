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

- problem_id: DegreeRigidity
- collection: openai-math
- question_id: openai-math:241
- source: openai-math
- source_locator: lean/ComparatorChallenges/DegreeRigidity.lean#OAI.TuringRigidity.ManuscriptMain.rigidity
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Every order automorphism of the Turing degrees is the identity, resolving their rigidity problem. Thus no nontrivial relabeling of degrees preserves the ordering by relative computability. ([Lean](lean/docs/241.md)) We prove that every order automorphism of the full partial order of Turing degrees is the identity, resolving the rigidity conjecture for the Turing degrees positively.
- notes: OpenAI math result family 241, Rigidity of the Turing degrees -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/241.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.TuringRigidity.ManuscriptMain.rigidity
- source_theorem_count: 1
- source_solution_module: OAI.Computability.DegreeRigidity.Main
- source_main_result: OAI.TuringRigidity.ManuscriptMain.rigidity
- source_papers: preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf
- source_scope_note: lean/docs/241.md
- source_field: Computability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace TuringRigidity

abbrev Oracle := ℕ → Bool

def oracleFunction (A : Oracle) : ℕ →. ℕ := fun n => Part.some (if A n then 1 else 0)

def Reduces (A B : Oracle) : Prop := TuringReducible (oracleFunction A) (oracleFunction B)

instance : IsPreorder Oracle Reduces where
  refl A := TuringReducible.refl (oracleFunction A)
  trans _ _ _ h k := TuringReducible.trans h k

def Degree := Antisymmetrization Oracle Reduces

instance : PartialOrder Degree :=
  @instPartialOrderAntisymmetrization Oracle
    { le := Reduces
      lt A B := Reduces A B ∧ ¬ Reduces B A
      lt_iff_le_not_ge _ _ := Iff.rfl
      le_refl A := TuringReducible.refl (oracleFunction A)
      le_trans _ _ _ h k := TuringReducible.trans h k }

private instance oraclePreorder : Preorder Oracle where
  le := Reduces
  lt A B := Reduces A B ∧ ¬ Reduces B A
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl A := TuringReducible.refl (oracleFunction A)
  le_trans _ _ _ h k := TuringReducible.trans h k

def MainTheorem : Prop := ∀ π : Degree ≃o Degree, ∀ a : Degree, π a = a

namespace ManuscriptMain

def rigidity_statement : Prop :=
  MainTheorem

end ManuscriptMain
end TuringRigidity

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.TuringRigidity.ManuscriptMain.rigidity_statement

end Problem

/- Formalization scope, from lean/docs/241.md: The rigidity problem asks whether the ordering of Turing degrees by relative computability has any nontrivial automorphism. The formalized result gives a negative answer: every order automorphism of the full Turing degrees of subsets of $\mathbb N$ fixes every degree, with no definability or genericity assumption. The additional representation corollaries are not included. -/
