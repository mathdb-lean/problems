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

- problem_id: ShortEgyptianFractions
- collection: openai-math
- question_id: openai-math:025
- source: openai-math
- source_locator: lean/ComparatorChallenges/ShortEgyptianFractions.lean#OAI.ShortEgyptian.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Every rational $`a/b`$ with $`1\le a\lt b`$ is a sum of $`O(\log\log b)`$ distinct positive unit fractions. The worst-case minimum number of terms has the same order, resolving Erdős’s conjecture on short Egyptian fractions. ([Lean](lean/docs/025.md)) We prove a conjecture of Erdős: for every sufficiently large integer b, every rational number $`a/b`$ with $`1\le a\lt b`$ is a sum of $`O(\log\log b)`$ distinct positive unit fractions, with an absolute implied constant. This order is best possible when the numerator varies. We also show that both the number of expansions of 1 with exactly k distinct terms and the least integer at least 2 that never occurs as a denominator in such an expansion grow doubly exponentially in k: their double logarithms have order k.
- notes: OpenAI math result family 025, Short Egyptian fractions -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/025.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ShortEgyptian.main
- source_theorem_count: 1
- source_solution_module: OAI.NumberTheory.ShortEgyptian.Main
- source_papers: preprints/Short-Egyptian-fractions-September-25-2026/Short-Egyptian-fractions-September-25-2026.pdf
- source_scope_note: lean/docs/025.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace ShortEgyptian

def IsExpansion (a b : ℕ) (ns : List ℕ) : Prop :=
  ns.Pairwise (· < ·) ∧ (∀ n ∈ ns, 2 ≤ n) ∧
    (ns.map (fun n => (1 : ℚ) / (n : ℚ))).sum = (a : ℚ) / (b : ℚ)

noncomputable def minLength (a b : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ ns : List ℕ, IsExpansion a b ns ∧ ns.length = k}

noncomputable def maxMinLength (b : ℕ) : ℕ :=
  (Finset.Ico 1 b).sup (fun a => minLength a b)

def main_statement : Prop :=
  (∀ a b : ℕ, 1 ≤ a → a < b → ∃ ns : List ℕ, IsExpansion a b ns) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ∀ b : ℕ, b₀ ≤ b →
        c₁ * Real.log (Real.log (b : ℝ)) ≤ (maxMinLength b : ℝ) ∧
        (maxMinLength b : ℝ) ≤ c₂ * Real.log (Real.log (b : ℝ))

end ShortEgyptian

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ShortEgyptian.main_statement

end Problem

/- Formalization scope, from lean/docs/025.md: An Egyptian-fraction expansion writes a rational number as a sum of distinct unit fractions. The formalization proves that every $a/b$ with $1\le a<b$ has such an expansion and that the largest minimum length at denominator $b$ is $\Theta(\log\log b)$. If $F(k)$ counts exact $k$-term expansions of $1$, it also proves $\log\log F(k)=\Theta(k)$ and bounds every denominator in such an expansion. Every integer $m\ge2$ occurs as a denominator in an expansion of $1$, with length eventually at most $(257/\log2+\varepsilon)\log\log m$ for every $\varepsilon>0$; padding can preserve that denominator. If $v(k)$ is the least integer at least $2$ absent from all exact $k$-term expansions of $1$, then eventually $e^{e^{k/600}}\le v(k)\le1+k^{2^{k-1}}$, and $\liminf_{k\to\infty}\log\log v(k)/k\ge\log2/257$. -/
