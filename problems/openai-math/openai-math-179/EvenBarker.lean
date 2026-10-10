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

- problem_id: EvenBarker
- collection: openai-math
- question_id: openai-math:179
- source: openai-math
- source_locator: lean/ComparatorChallenges/EvenBarker.lean#OAI.CirculantHadamard.Barker.even_length_eq_two_or_four
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that real circulant Hadamard matrices exist exactly in orders 1 and 4, resolving the circulant Hadamard conjecture. Together with classical Barker-sequence results, this shows that binary sequences whose nontrivial aperiodic autocorrelations have magnitude at most 1 exist at lengths n &gt; 1 exactly when $`n\in\{2,3,4,5,7,11,13\}`$. ([Lean](lean/docs/179.md)) We prove the circulant Hadamard conjecture: a real circulant Hadamard matrix has order 1 or 4. As a consequence, Barker sequences of length greater than one exist exactly at lengths 2, 3, 4, 5, 7, 11, 13, proving the Barker-sequence conjecture.
- notes: OpenAI math result family 179, The circulant Hadamard and Barker-sequence conjectures -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/179.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CirculantHadamard.Barker.even_length_eq_two_or_four
- source_theorem_count: 1
- source_solution_module: OAI.LinearAlgebra.Barker.Main
- source_papers: preprints/The-circulant-Hadamard-conjecture-September-23-2026/paper.pdf
- source_scope_note: lean/docs/179.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace CirculantHadamard

universe u

def IsSign {R : Type u} [One R] [Neg R] (x : R) : Prop :=
  x = 1 ∨ x = -1

namespace Barker
open scoped BigOperators

def aperiodic {n : ℕ} (h : Fin n → ℤ) (k : ℕ) : ℤ :=
  ∑ j : Fin (n - k), h ⟨j.val, by omega⟩ * h ⟨j.val + k, by omega⟩

def IsBarker {n : ℕ} (h : Fin n → ℤ) : Prop :=
  (∀ j, IsSign (h j)) ∧ ∀ k : ℕ, 0 < k → k < n → |aperiodic h k| ≤ 1

def even_length_eq_two_or_four_statement : Prop :=
  ∀ {n : ℕ} (h : Fin n → ℤ) (hnpos : 0 < n) (hn : Even n) (hb : IsBarker h),
    n = 2 ∨ n = 4

end Barker
end CirculantHadamard

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.CirculantHadamard.Barker.even_length_eq_two_or_four_statement

end Problem

/- Formalization scope, from lean/docs/179.md: The formalization proves the circulant Hadamard conjecture in exact form: a real circulant Hadamard matrix of positive order $n$ exists exactly when $n=1$ or $n=4$. Explicit witnesses are supplied for both orders, with no restriction on prime factors. It also proves the even-length part of the Barker-sequence consequence. A positive even-length sign sequence whose nonzero aperiodic autocorrelations have absolute value at most one must have length $2$ or $4$. The paper's classification of odd Barker lengths is outside this selected additional statement. -/
