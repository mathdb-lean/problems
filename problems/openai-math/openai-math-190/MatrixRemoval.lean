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

- problem_id: MatrixRemoval
- collection: openai-math
- question_id: openai-math:190
- source: openai-math
- source_locator: lean/ComparatorChallenges/MatrixRemoval.lean#OAI.Problem348.no_polynomial_removal_bound
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Disproves polynomial ordered binary matrix removal with one fixed $`66\times66`$ zero–one pattern. Matrices can require many binary-entry changes to become pattern-free while their copy density is smaller than every proposed polynomial bound in that distance. Copies preserve row and column orders and match both zeros and ones. ([Lean](lean/docs/190.md)) We construct a fixed $`66\times66`$ binary matrix for which ordered matrix removal has no polynomial bound. This disproves the polynomial ordered binary matrix-removal conjecture. Ordered copies preserve the separate row and column orders and match both zeros and ones; removal permits changing entries in either direction.
- notes: OpenAI math result family 190, Polynomial removal fails for ordered binary matrices -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/190.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Problem348.no_polynomial_removal_bound
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.MatrixRemoval.Main
- source_main_result: OAI.Problem348.no_polynomial_removal_bound
- source_papers: preprints/Polynomial-removal-fails-for-ordered-binary-matrices-September-25-2026/paper.pdf
- source_scope_note: lean/docs/190.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

namespace Problem348

abbrev BinaryMatrix (n : ℕ) := Fin n → Fin n → Bool

abbrev IncreasingMap (k n : ℕ) := {f : Fin k → Fin n // StrictMono f}

def orderedCopies {k n : ℕ} (H : BinaryMatrix k) (A : BinaryMatrix n) :
    Finset (IncreasingMap k n × IncreasingMap k n) := by
  classical
  exact Finset.univ.filter (fun rc =>
    ∀ i j, A ((rc.1).val i) ((rc.2).val j) = H i j)

def copyCount {k n : ℕ} (H : BinaryMatrix k) (A : BinaryMatrix n) : ℕ :=
  (orderedCopies H A).card

def HFree {k n : ℕ} (H : BinaryMatrix k) (A : BinaryMatrix n) : Prop :=
  copyCount H A = 0

def hammingDistance {n : ℕ} (A B : BinaryMatrix n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun rc : Fin n × Fin n =>
    A rc.1 rc.2 ≠ B rc.1 rc.2)).card

def etaBit (a b : ℕ) : Bool :=
  decide (((a / (2 ^ (5 - b))) % 2) = 1)

def anchor64 (u v : Fin 64) : Bool :=
  if 32 ≤ u.val ∧ 59 ≤ v.val then
    etaBit (u.val - 32) (v.val - 58)
  else
    decide (u.val ≠ v.val)

def fixedH : BinaryMatrix 66 := fun u v =>
  if hu : u.val < 64 then
    if hv : v.val < 64 then
      anchor64 ⟨u.val, hu⟩ ⟨v.val, hv⟩
    else
      decide ((v.val = 64 ∧ u.val = 0) ∨
        (v.val = 65 ∧ u.val = 1))
  else
    if v.val < 64 then
      decide ((u.val = 64 ∧ v.val = 0) ∨
        (u.val = 65 ∧ v.val = 1))
    else
      decide (u.val = 65 ∨ v.val = 64)

def fixedMinEdits {n : ℕ} (A : BinaryMatrix n) : ℕ := by
  classical
  exact
    (Finset.univ.image (fun B : BinaryMatrix n =>
      if HFree fixedH B then hammingDistance A B else n * n + 1)).min'
      (by simp)

def fixedDistance {n : ℕ} (A : BinaryMatrix n) : ℝ :=
  (fixedMinEdits A : ℝ) / ((n : ℝ) ^ 2)

def no_polynomial_removal_bound_statement : Prop :=
  ∀ c C : ℝ, 0 < c → 0 < C →
  ∃ n : ℕ, 1 ≤ n ∧
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∃ A : BinaryMatrix n,
        fixedDistance A ≥ ε ∧
        (copyCount fixedH A : ℝ) <
          c * Real.rpow ε C * ((n : ℝ) ^ 132)

end Problem348

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Problem348.no_polynomial_removal_bound_statement

end Problem

/- Formalization scope, from lean/docs/190.md: The formalized result disproves a polynomial removal bound for one explicit $66\times66$ binary pattern. For every $c,C>0$, there is an $n\times n$ binary matrix at normalized edit distance at least $\varepsilon>0$ from being pattern-free but with fewer than $c\varepsilon^C n^{132}$ induced ordered copies. Row and column indices are independently increasing, and every zero and one entry must match. The construction gives an explicit sequence of such matrices, allowing edits in both directions. -/
