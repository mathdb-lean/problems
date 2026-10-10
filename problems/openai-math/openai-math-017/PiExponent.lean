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

- problem_id: PiExponent
- collection: openai-math
- question_id: openai-math:017
- source: openai-math
- source_locator: lean/ComparatorChallenges/PiExponent.lean#OAI.PiExponent.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that the irrationality exponent of π is exactly 2: for every ε &gt; 0 and all sufficiently large denominators q, every rational $`p/q`$ satisfies $`|\pi-p/q|\ge q^{-2-\varepsilon}`$. This also proves convergence of the Flint–Hills series $`\sum_{n\ge1}1/(n^3\sin^2 n)`$, with angles in radians. ([Lean](lean/docs/017.md)) We prove the conjecture that the irrationality exponent of π is 2. As a consequence, the classical Flint–Hills series $`\sum_{n\ge1}1/(n^3\sin^2 n)`$ converges, with angles in radians.
- notes: OpenAI math result family 017, The irrationality exponent of <i>π</i> is 2 -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/017.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.PiExponent.main
- source_theorem_count: 1
- source_solution_module: OAI.NumberTheory.PiExponent.Main
- source_papers: preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf
- source_scope_note: lean/docs/017.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace PiExponent

def main_statement : Prop :=
  (∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
    ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) ∧
  sSup {ν : ℝ | 0 < ν ∧
    Set.Infinite {r : ℚ | 2 ≤ r.den ∧
      0 < |Real.pi - (r : ℝ)| ∧
      |Real.pi - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}} = 2

end PiExponent

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.PiExponent.main_statement

end Problem

/- Formalization scope, from lean/docs/017.md: The formalization proves that the irrationality exponent of $\pi$ is exactly two. For every $\nu>2$, all sufficiently large positive denominators $q$ satisfy $|\pi-p/q|\ge q^{-\nu}$ for every integer numerator $p$. It also states the exact supremum characterization using infinitely many rational approximations. The paper's convergence consequence for the Flint–Hills series is outside this selected statement. -/
