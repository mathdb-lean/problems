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

- problem_id: ErdosReciprocal
- collection: openai-math
- question_id: openai-math:159
- source: openai-math
- source_locator: lean/ComparatorChallenges/ErdosReciprocal.lean#OAI.Erdos3.manuscriptReciprocalProgressionTheorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Erdős's conjecture that every set of positive integers with divergent reciprocal sum contains arithmetic progressions of every finite length. Quantitatively, for each fixed k ≥ 3, every subset of $`\{1,\ldots,N\}`$ with no nonconstant k-term progression has size at most $`C_kN\exp[-c_k(\log N)^{\varepsilon_k}]`$, with positive constants depending only on k. ([Lean](lean/docs/159.md)) We prove Erdős's conjecture that every set of positive integers with divergent reciprocal sum contains arithmetic progressions of every finite length. More quantitatively, for every fixed k ≥ 3, we show
- notes: OpenAI math result family 159, Erdős’s reciprocal-sum conjecture and quasipolynomial Szemerédi bounds -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/159.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Erdos3.manuscriptReciprocalProgressionTheorem
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.Progressions.Main
- source_papers: preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf
- source_scope_note: lean/docs/159.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace Erdos3

def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

end Erdos3

open scoped BigOperators

namespace Erdos3

noncomputable def reciprocalTerm (A : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact if n ∈ A then (n : ℝ)⁻¹ else 0

end Erdos3

namespace Erdos3

def ReciprocalProgressionTheorem : Prop :=
  ∀ A : Set ℕ, ¬ Summable (reciprocalTerm A) → ∀ k : ℕ, HasAP A k

end Erdos3

namespace Erdos3

def manuscriptReciprocalProgressionTheorem_statement : Prop :=
  ReciprocalProgressionTheorem

end Erdos3

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Erdos3.manuscriptReciprocalProgressionTheorem_statement

end Problem

/- Formalization scope, from lean/docs/159.md: Erdős's reciprocal-sum conjecture asks whether every set of positive integers with divergent reciprocal sum contains arithmetic progressions of every finite length. The formalization proves this statement: for every requested length, such a set contains a progression with positive common difference. The selected theorem is the reciprocal-sum consequence. The paper's quantitative upper bound for the largest progression-free subset of $\{1,\ldots,N\}$ is outside this statement. -/
