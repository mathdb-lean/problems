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

- problem_id: SteinitzBergstrom
- collection: openai-math
- question_id: openai-math:097
- source: openai-math
- source_locator: lean/ComparatorChallenges/SteinitzBergstrom.lean#OAI.EuclideanSteinitzBergstrom.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that any finite sequence in the Euclidean unit ball of ℝd admits signs keeping every partial sum within $`C\sqrt d`$, independently of length. Consequently every zero-sum family can be reordered with the same bound on unsigned partial sums. A matching lower bound gives the optimal order $`S_2(d)=\Theta(\sqrt d)`$. ([Lean](lean/docs/097.md)) Every prescribed-order finite sequence of vectors in the Euclidean unit ball of ℝd has one signing for which every signed prefix has norm at most $`C\sqrt d`$, with C absolute and independent of the sequence length. Consequently, every indexed zero-sum family of unit-ball vectors admits an ordering with the same bound for its unsigned partial sums. This determines the Euclidean Steinitz constant up to absolute factors, $`S_2(d)=\Theta(\sqrt d)`$, and resolves the Euclidean Steinitz–Bergström conjecture.
- notes: OpenAI math result family 097, The Euclidean Steinitz–Bergström bound -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/097.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.EuclideanSteinitzBergstrom.main
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.Steinitz.Main
- source_main_result: OAI.EuclideanSteinitzBergstrom.main
- source_papers: preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026.pdf
- source_scope_note: lean/docs/097.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace EuclideanSteinitzBergstrom

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

def SignedPrefixBound (C : ℝ) : Prop :=
  ∀ (d N : ℕ), 1 ≤ d → 1 ≤ N →
    ∀ (v : Fin N → Vector d), (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin N → ℝ, (∀ i, ε i = -1 ∨ ε i = 1) ∧
        ∀ k : ℕ, k ≤ N →
          ‖∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), ε i • v i‖ ≤
            C * Real.sqrt d

def OrderingPrefixBound (C : ℝ) : Prop :=
  ∀ (d N : ℕ), 1 ≤ d → 1 ≤ N →
    ∀ (v : Fin N → Vector d), (∀ i, ‖v i‖ ≤ 1) → (∑ i, v i) = 0 →
      ∃ π : Equiv.Perm (Fin N), ∀ k : ℕ, k ≤ N →
        ‖∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), v (π i)‖ ≤
          C * Real.sqrt d

def main_statement : Prop :=
  ∃ C : ℝ, SignedPrefixBound C ∧ OrderingPrefixBound C

end EuclideanSteinitzBergstrom

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.EuclideanSteinitzBergstrom.main_statement

end Problem

/- Formalization scope, from lean/docs/097.md: The formalized result gives the Euclidean Steinitz–Bergström bound with one absolute constant $C$. For every finite family of vectors in the unit ball of $\mathbb R^d$, signs can be chosen so that every prefix in the prescribed order has norm at most $C\sqrt d$. When the vector sum is zero, a permutation makes every unsigned prefix satisfy the same bound. Repeated and zero vectors are included. The result is existential and does not supply an online algorithm. -/
