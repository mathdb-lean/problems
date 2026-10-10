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

- problem_id: RamseyFive
- collection: openai-math
- question_id: openai-math:170
- source: openai-math
- source_locator: lean/ComparatorChallenges/RamseyFive.lean#OAI.SharpRamseyFive.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For every fixed integer s ≥ 5, proves $`r(s,t)=t^{s-1}/(\log t)^{s-2+o(1)}`$ as $`t\to\infty`$, determining the logarithmic exponent and matching the classical upper bound at that scale. Here $`r(s,t)`$ is the least number of vertices forcing an s-clique or a t-vertex independent set. ([Lean](lean/docs/170.md)) We determine the sharp logarithmic exponent of the off-diagonal Ramsey number $`r(5,t)`$: For every fixed integer s ≥ 6, we determine the sharp logarithmic exponent of the off-diagonal Ramsey number:
- notes: OpenAI math result family 170, Sharp logarithmic exponents for off-diagonal Ramsey numbers -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/170.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SharpRamseyFive.main
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.RamseyFive.Main
- source_papers: preprints/The-Sharp-Logarithmic-Exponent-of-r-5-t-September-24-2026/paper.pdf preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf
- source_scope_note: lean/docs/170.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace SharpRamseyFive

def RamseyProperty (s t n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ A : Finset (Fin n), G.IsNClique s A) ∨
    (∃ B : Finset (Fin n), G.IsNIndepSet t B)

noncomputable def ramsey (s t : ℕ) : ℕ := sInf {n : ℕ | RamseyProperty s t n}

def SharpBounds : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    (t : ℝ) ^ 4 / Real.rpow (Real.log t) (3 + ε) ≤ (ramsey 5 t : ℝ) ∧
    (ramsey 5 t : ℝ) ≤ C * (t : ℝ) ^ 4 / (Real.log t) ^ 3

def SharpExponent : Prop :=
  Filter.Tendsto
    (fun t : ℕ => (4 * Real.log (t : ℝ) - Real.log (ramsey 5 t : ℝ)) /
      Real.log (Real.log (t : ℝ)))
    Filter.atTop (nhds (3 : ℝ))

def main_statement : Prop :=
  SharpBounds ∧ SharpExponent

end SharpRamseyFive

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SharpRamseyFive.main_statement

end Problem

/- Formalization scope, from lean/docs/170.md: The formalization determines the sharp logarithmic exponent of the off-diagonal Ramsey number $r(5,t)$. It proves $r(5,t)=t^4/(\log t)^{3+o(1)}$ as $t\to\infty$. For every $\varepsilon>0$, the lower bound $t^4/(\log t)^{3+\varepsilon}$ holds eventually, while the upper bound is $Ct^4/(\log t)^3$ for an absolute $C>0$. The corresponding logarithmic exponent converges to three along all natural values of $t$. The formalization determines the sharp logarithmic exponent of the off-diagonal Ramsey number for every fixed integer $s\ge6$. It proves $r(s,t)=t^{s-1}/(\log t)^{s-2+o(1)}$ as $t\to\infty$. More explicitly, for each $\varepsilon>0$ the lower bound $t^{s-1}/(\log t)^{s-2+\varepsilon}$ holds eventually, while the upper bound is $C_s t^{s-1}/(\log t)^{s-2}$. The logarithmic exponent limit is taken along all natural values of $t$. -/
