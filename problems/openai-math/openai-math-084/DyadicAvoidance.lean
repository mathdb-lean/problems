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

- problem_id: DyadicAvoidance
- collection: openai-math
- question_id: openai-math:084
- source: openai-math
- source_locator: lean/ComparatorChallenges/DyadicAvoidance.lean#OAI.Problem310.dyadic_affine_avoidance
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For every fixed $`q\in(0,1)`$, constructs compact subsets of $`[0,1]`$ with measure arbitrarily close to one containing no translated and nontrivially dilated copy of $`\{q^n:n\ge1\}`$, with dilations of either sign. This resolves the geometric-progression case of the Erdős similarity conjecture for every ratio. ([Lean](lean/docs/084.md)) We construct a compact subset of the unit interval, of measure arbitrarily close to one, that contains no affine copy of the dyadic sequence $`\{2^{-n}:n\ge1\}`$. The conclusion holds for every translation and every nonzero real dilation, of either sign, proving the dyadic case of the Erdős similarity conjecture.
- notes: OpenAI math result family 084, The geometric case of the Erdős similarity conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/084.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Problem310.dyadic_affine_avoidance
- source_theorem_count: 1
- source_solution_module: OAI.MeasureTheory.DyadicAvoidance.Main
- source_papers: preprints/The-dyadic-case-of-the-Erdos-similarity-conjecture-September-25-2026/paper.pdf
- source_scope_note: lean/docs/084.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

namespace Problem310

def dyadicPoint (n : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ n

def dyadic_affine_avoidance_statement : Prop :=
  ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧
      MeasureTheory.volume E > ENNReal.ofReal (1 - η) ∧
      ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧
        x + s * dyadicPoint n ∉ E

end Problem310

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Problem310.dyadic_affine_avoidance_statement

end Problem

/- Formalization scope, from lean/docs/084.md: The formalization proves the dyadic case of the Erdős similarity conjecture. For every $0<\eta<1$, it constructs a compact set $E\subset[0,1]$ of measure greater than $1-\eta$ that contains no affine copy of $\{2^{-n}:n\ge1\}$. Explicitly, for every translation $x$ and every nonzero real dilation $s$, some point $x+s2^{-n}$ lies outside $E$. Both signs of $s$ are included. -/
