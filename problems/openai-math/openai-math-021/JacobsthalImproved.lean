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

- problem_id: JacobsthalImproved
- collection: openai-math
- question_id: openai-math:021
- source: openai-math
- source_locator: lean/ComparatorChallenges/JacobsthalImproved.lean#OAI.Erdos970.Erdos970Final.erdos_970_iterated_log
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Answers Jacobsthal's quadratic-bound question: every interval of $`Ck^2`$ consecutive integers contains an integer coprime to any prescribed positive integer with at most k distinct prime divisors, for an absolute constant C. The bound is uniform over prime sets and interval positions and removes the classical logarithmic loss. ([Lean](lean/docs/021.md)) Let $`h(k)`$ be the least integer such that every interval of $`h(k)`$ consecutive integers contains an integer coprime to any prescribed positive integer having at most k distinct prime divisors. We prove $`h(k)\ll k^2/(\log\log(3k))^2`$, giving an affirmative answer to Jacobsthal's quadratic-bound question.
- notes: OpenAI math result family 021, A quadratic bound for Jacobsthal’s function -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/021.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Erdos970.Erdos970Final.erdos_970_iterated_log
- source_theorem_count: 1
- source_solution_module: OAI.NumberTheory.Jacobsthal.Main
- source_papers: preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf
- source_scope_note: lean/docs/021.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace Erdos970

namespace NumberTheoryLean.Targets

def IsJacobsthalBound (k m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n

def JacobsthalIteratedLog : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
    ∃ m : ℕ, IsJacobsthalBound k m ∧
      (m : ℝ) ≤ C * (k : ℝ) ^ 2 / (Real.log (Real.log (3 * (k : ℝ)))) ^ 2

end NumberTheoryLean.Targets

namespace Erdos970Final

def erdos_970_iterated_log_statement : Prop :=
  NumberTheoryLean.Targets.JacobsthalIteratedLog

end Erdos970Final

end Erdos970

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Erdos970.Erdos970Final.erdos_970_iterated_log_statement

end Problem

/- Formalization scope, from lean/docs/021.md: Let $h(k)$ be the least interval length that guarantees an integer coprime to any prescribed positive modulus with at most $k$ distinct prime factors. The formalization proves the paper's strengthened Jacobsthal bound $h(k)\le Ck^2/(\log\log(3k))^2$ for one absolute $C>0$ and every $k\ge1$. Intervals may begin at any signed integer. The earlier quadratic bound is also retained as a separate statement; the optimal order of growth is not determined. -/
