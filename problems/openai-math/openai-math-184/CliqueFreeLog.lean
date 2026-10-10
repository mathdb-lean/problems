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

- problem_id: CliqueFreeLog
- collection: openai-math
- question_id: openai-math:184
- source: openai-math
- source_locator: lean/ComparatorChallenges/CliqueFreeLog.lean#OAI.CliqueFreeLog.logarithmic_independence_bound
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the Alon–Krivelevich–Sudakov coloring conjecture in correspondence-coloring form: graphs avoiding any fixed subgraph F need $`O_F(\Delta/\log\Delta)`$ colors when their maximum degree Δ is sufficiently large. Also proves the Ajtai–Erdős–Komlós–Szemerédi independence conjecture: for fixed r ≥ 4, every n-vertex Kr-free graph of average degree d ≥ 2 has an independent set of size $`\Omega_r(n\log d/d)`$. ([Lean](lean/docs/184.md)) For every fixed integer r ≥ 4, every Kr-free graph on n vertices with average degree d ≥ 2 has an independent set of size at least $`c_r n\log d/d`$, where $`c_r\gt 0`$ depends only on r. This proves the fixed-clique-size independence conjecture of Ajtai, Erdős, Komlós and Szemerédi.
- notes: OpenAI math result family 184, Correspondence coloring with a fixed forbidden subgraph -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/184.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CliqueFreeLog.logarithmic_independence_bound
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.CliqueFree.Main
- source_main_result: OAI.CliqueFreeLog.logarithmic_independence_bound
- source_papers: preprints/A-Logarithmic-Independence-Bound-for-Clique-Free-Graphs-September-25-2026/paper.pdf
- source_scope_note: lean/docs/184.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace CliqueFreeLog

noncomputable def averageDegree {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := by
  classical
  exact 2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)

def logarithmic_independence_bound_statement : Prop :=
  ∀ (r : ℕ) (hr : 4 ≤ r),
    ∃ c : ℝ, 0 < c ∧
      ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
        G.CliqueFree r → 2 ≤ averageDegree G →
        c * (Fintype.card V : ℝ) * Real.log (averageDegree G) / averageDegree G ≤
          (G.indepNum : ℝ)

end CliqueFreeLog

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.CliqueFreeLog.logarithmic_independence_bound_statement

end Problem

/- Formalization scope, from lean/docs/184.md: The formalized result gives a logarithmic improvement in the independence number of clique-free graphs. For every fixed integer $r\ge4$, there is $c_r>0$ such that every finite $K_r$-free simple graph on $n$ vertices with average degree $d\ge2$ has an independent set of size at least $c_r n\log d/d$. The constant depends only on $r$. -/
