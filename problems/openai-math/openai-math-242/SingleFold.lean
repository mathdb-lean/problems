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

- problem_id: SingleFold
- collection: openai-math
- question_id: openai-math:242
- source: openai-math
- source_locator: lean/ComparatorChallenges/SingleFold.lean#OAI.SingleFold.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Every recursively enumerable set of tuples of natural numbers has a Diophantine representation with exactly one auxiliary solution for each member and none for nonmembers. This proves the single-fold conjecture and hence the finite-fold conjecture. Diophantine solvability over the nonnegative integers remains undecidable even with an at-most-one-solution promise. ([Lean](lean/docs/242.md)) Every recursively enumerable set of natural-number tuples has a polynomial Diophantine representation with exactly one complete auxiliary tuple for each member. This proves the single-fold conjecture and, consequently, the finite-fold conjecture.
- notes: OpenAI math result family 242, Single-fold Diophantine representations and undecidability under an at-most-one-solution promise -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/242.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SingleFold.main
- source_theorem_count: 1
- source_solution_module: OAI.NumberTheory.SingleFold.Main
- source_main_result: OAI.SingleFold.main
- source_papers: preprints/Single-fold-Diophantine-representations-September-24-2026/paper.pdf
- source_scope_note: lean/docs/242.md
- source_field: NumberTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace SingleFold

/-- Evaluation over the integers of an integer polynomial at natural inputs. -/
noncomputable def evalNat {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (a : Fin n → ℕ) (w : Fin m → ℕ) : ℤ :=
  MvPolynomial.eval (Sum.elim (fun i => (a i : ℤ)) (fun j => (w j : ℤ))) P

/-- Exact existence on members, no witness on nonmembers, and uniqueness of the
whole witness on every input. No coordinates are hidden outside `w`. -/
def Represents {n m : ℕ} (P : MvPolynomial (Fin n ⊕ Fin m) ℤ)
    (S : Set (Fin n → ℕ)) : Prop :=
  ∀ a, (a ∈ S ↔ ∃ w, evalNat P a w = 0) ∧
    ∀ w v, evalNat P a w = 0 → evalNat P a v = 0 → w = v

/-- Single-fold representation with positive input and witness lengths. -/
def MainStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (S : Set (Fin n → ℕ)), REPred (fun a => a ∈ S) →
    ∃ (m : ℕ), 1 ≤ m ∧ ∃ P : MvPolynomial (Fin n ⊕ Fin m) ℤ, Represents P S

def main_statement : Prop :=
  MainStatement

end SingleFold

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SingleFold.main_statement

end Problem

/- Formalization scope, from lean/docs/242.md: The single-fold Diophantine conjecture asks whether every recursively enumerable set has a polynomial representation with a unique auxiliary witness for each member. The formalization establishes this for every recursively enumerable subset of $\mathbb N^n$, $n\ge1$: an integer polynomial has exactly one complete natural-number witness tuple for members and none for nonmembers. The consequence that solvability remains undecidable under an at-most-one-solution promise is not separately formalized. -/
