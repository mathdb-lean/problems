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

- problem_id: QuantitativeVanDerWaerden
- collection: openai-math
- question_id: openai-math:160
- source: openai-math
- source_locator: lean/ComparatorChallenges/QuantitativeVanDerWaerden.lean#OAI.QuantitativeVanDerWaerden.uniform_lower_bound
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves Erdős's superexponential-growth question for van der Waerden numbers. If $`W_r(k)`$ is the least interval length forcing a monochromatic k-term progression in every r-coloring, then $`W_r(k)\gt k^{ck\lfloor\log_2 r\rfloor}`$ for an absolute c &gt; 0, all r ≥ 2 and sufficiently large k, uniformly in r. In particular, $`W_r(k)^{1/k}\to\infty`$ for each fixed r. ([Lean](lean/docs/160.md)) We prove that there are absolute constants c &gt; 0 and K0 such that $`W_r(k)\gt k^{ck\lfloor\log_2 r\rfloor}`$ for every $`k\ge K_0`$ and r ≥ 2. Consequently $`W_r(k)^{1/k}\to\infty`$ for each fixed r ≥ 2, giving a quantitative positive resolution of Erdős's superexponential-growth question, including the two-color case.
- notes: OpenAI math result family 160, Superexponential van der Waerden numbers -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/160.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.QuantitativeVanDerWaerden.uniform_lower_bound
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.ProgressionColoring.Main
- source_main_result: OAI.QuantitativeVanDerWaerden.uniform_lower_bound
- source_papers: preprints/Quantitative-Superexponential-Bounds-for-van-der-Waerden-Numbers-September-23-2026/paper.pdf
- source_scope_note: lean/docs/160.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

universe u

namespace QuantitativeVanDerWaerden

def MonoAP {α : Type u} (c : ℕ → α) (k a d : ℕ) : Prop :=
  ∀ j < k, c (a + j * d) = c a

def HasMonoAP {α : Type u} (c : ℕ → α) (k N : ℕ) : Prop :=
  ∃ a d, 0 < d ∧ a + (k - 1) * d < N ∧ MonoAP c k a d

def IsRamsey (α : Type u) (k N : ℕ) : Prop :=
  ∀ c : ℕ → α, HasMonoAP c k N

/-- The least positive Ramsey interval size. Statements about its Ramsey
property require a finiteness proof; no such proof is built into this definition. -/
noncomputable def W (r k : ℕ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ IsRamsey (Fin r) k N}

open Filter

/-- An absolute quantitative lower bound, uniform over all color counts. -/
def uniform_lower_bound_statement : Prop :=
  ∃ K : ℕ, ∀ k ≥ K, ∀ r ≥ 2,
      (k : ℝ) ^ ((1 / 100000 : ℝ) * k * (Nat.log 2 r : ℝ)) < (W r k : ℝ)

end QuantitativeVanDerWaerden

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.QuantitativeVanDerWaerden.uniform_lower_bound_statement

end Problem

/- Formalization scope, from lean/docs/160.md: Let $W(r,k)$ be the least interval length forcing a monochromatic $k$-term arithmetic progression in every coloring with at most $r$ colors. The formalized result gives an absolute threshold $K$ such that $W(r,k)>k^{k\lfloor\log_2 r\rfloor/100000}$ for all $k\ge K$ and $r\ge2$. It also establishes the associated growth limits, finiteness, and boundary values. The sharper intermediate estimates used in the paper are not part of the described formalization. -/
