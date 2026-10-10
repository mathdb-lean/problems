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

- problem_id: CycleCliqueRamsey
- collection: openai-math
- question_id: openai-math:189
- source: openai-math
- source_locator: lean/ComparatorChallenges/CycleCliqueRamsey.lean#OAI.CycleClique.thm_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the Erdős–Faudree–Rousseau–Schelp conjecture: $`R(C_m,K_n)=(m-1)(n-1)+1`$ for every $`m\ge n\ge3`$, except $`R(C_3,K_3)=6`$. This is the exact threshold forcing a red m-cycle or a blue n-clique in every red–blue coloring of a complete graph. ([Lean](lean/docs/189.md)) We prove that $`R(C_m,K_n)=(m-1)(n-1)+1`$ for every pair of integers $`m\ge n\ge3`$ other than $`(m,n)=(3,3)`$, for which $`R(C_3,K_3)=6`$. This establishes the cycle–clique conjecture of Erdős, Faudree, Rousseau and Schelp. The proof combines expansion in a minimal counterexample with a large-clique lemma and an optimization of paths joining clique vertices. These arguments reduce the remaining cases to $`3{,}099`$ finite parameter-pattern instances, which are excluded by two exact implementations of proved inference rules. Complete programs and deduction traces accompany the paper.
- notes: OpenAI math result family 189, Cycle–clique Ramsey numbers -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/189.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CycleClique.thm_main
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.Ramsey.CycleClique.Main
- source_papers: preprints/Cycle-clique-Ramsey-numbers-September-25-2026/Cycle-clique-Ramsey-numbers-September-25-2026.pdf
- source_scope_note: lean/docs/189.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

 

namespace CycleClique
open scoped SimpleGraph

 

def RamseyProperty (m n N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    SimpleGraph.cycleGraph m ⊑ G ∨ (⊤ : SimpleGraph (Fin n)) ⊑ Gᶜ

 

noncomputable def cycleCliqueRamsey (m n : ℕ) : ℕ :=
  sInf {N : ℕ | RamseyProperty m n N}

 

def thm_main_statement : Prop :=
  (∀ m n : ℤ, n ≤ m → 3 ≤ n → (m, n) ≠ (3, 3) →
      (cycleCliqueRamsey m.toNat n.toNat : ℤ) = (m - 1) * (n - 1) + 1) ∧
    cycleCliqueRamsey 3 3 = 6

end CycleClique

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.CycleClique.thm_main_statement

end Problem

/- Formalization scope, from lean/docs/189.md: The cycle–clique Ramsey conjecture predicts the exact number of vertices forcing either a cycle $C_m$ or a clique $K_n$ in complementary colors. The formalization proves $R(C_m,K_n)=(m-1)(n-1)+1$ for all integers $m\ge n\ge3$ except $(m,n)=(3,3)$, where it proves $R(C_3,K_3)=6$. This is the complete parameter range of the paper's main theorem. -/
