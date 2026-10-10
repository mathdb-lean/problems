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

- problem_id: SquareDifference
- collection: openai-math
- question_id: openai-math:182
- source: openai-math
- source_locator: lean/ComparatorChallenges/SquareDifference.lean#OAI.SquareDifference.power_saving
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For every fixed intersective integer polynomial h of degree k ≥ 2 with positive leading coefficient, proves that a subset of $`\{1,\ldots,N\}`$ avoiding nonzero values $`h(1),h(2),\ldots`$ as differences has size $`O_h(N^{1-c_k})`$, with $`c_k\gt 0`$ depending only on degree. Here intersective means having a root modulo every modulus. For prime arguments, a power saving also holds when h has a unit root modulo every modulus, with exponent allowed to depend on h. ([Lean](lean/docs/182.md)) We prove that there are absolute constants c &gt; 0 and C &lt; ∞ such that every set $`A\subseteq\{1,\ldots,N\}`$ with no nonzero square difference satisfies $`|A|\le C N^{1-c}`$. This answers the fixed-power question posed by Green and Sawhney.
- notes: OpenAI math result family 182, Power savings for intersective polynomial differences and prime arguments -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/182.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SquareDifference.power_saving
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.SquareDifference.Main
- source_papers: preprints/A-power-saving-for-square-difference-free-sets-September-24-2026/paper.pdf
- source_scope_note: lean/docs/182.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace SquareDifference

def IsSquareDifferenceFree (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ m : ℕ, 1 ≤ m → a - b ≠ (m : ℤ) ^ 2

def power_saving_statement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℤ,
      A ⊆ Finset.Icc 1 (N : ℤ) → SquareDifference.IsSquareDifferenceFree A →
        (A.card : ℝ) ≤ C * (N : ℝ) ^ (1 - c)

end SquareDifference

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SquareDifference.power_saving_statement

end Problem

/- Formalization scope, from lean/docs/182.md: The formalization proves a fixed power saving for sets with no nonzero square difference. There are absolute constants $c>0$ and $C$ such that every $A\subseteq\{1,\ldots,N\}$ satisfying $a-b\ne m^2$ for all $a,b\in A$ and integers $m\ge1$ has $|A|\le C N^{1-c}$. The bound is uniform for every integer $N\ge1$. -/
