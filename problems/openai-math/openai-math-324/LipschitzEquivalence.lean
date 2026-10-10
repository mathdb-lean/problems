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

- problem_id: LipschitzEquivalence
- collection: openai-math
- question_id: openai-math:324
- source: openai-math
- source_locator: lean/ComparatorChallenges/LipschitzEquivalence.lean#OAI.LipschitzCounterexample.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs separable real Banach spaces that are globally bi-Lipschitz equivalent but not linearly isomorphic, resolving the separable Lipschitz-isomorphism problem negatively. Thus even the complete metric structure up to bi-Lipschitz equivalence does not determine a separable Banach space's linear isomorphism class. ([Lean](lean/docs/324.md)) There are separable real Banach spaces that are globally bi-Lipschitz equivalent but not linearly isomorphic. This gives a negative answer to the separable Banach-space Lipschitz-isomorphism problem. We construct a separable real Banach space Z that contains no linear copy of c0, yet is bi-Lipschitz equivalent to $`Z\oplus_\infty c_0`$. The same space contains a bi-Lipschitz image of every separable metric space.
- notes: OpenAI math result family 324, Lipschitz equivalent Banach spaces need not be linearly isomorphic -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/324.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.LipschitzCounterexample.main
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.LipschitzEquivalence.Main
- source_main_result: OAI.LipschitzCounterexample.main
- source_papers: preprints/Lipschitz-Equivalent-Separable-Banach-Spaces-Need-Not-Be-Linearly-Isomorphic-September-24-2026/paper.pdf preprints/Bi-Lipschitz-Absorption-of-c0-Without-a-Linear-Copy-of-c0-September-26-2026/paper.pdf
- source_scope_note: lean/docs/324.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

universe uE uF

noncomputable section
namespace LipschitzCounterexample

abbrev RealL2 := lp (fun _ : ℕ => ℝ) 2
abbrev C0L2 := ZeroAtInftyContinuousMap ℕ RealL2

structure SeparableRealBanach where
  Carrier : Type
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [normedSpace : NormedSpace ℝ Carrier]
  [completeSpace : CompleteSpace Carrier]
  [separableSpace : TopologicalSpace.SeparableSpace Carrier]

attribute [instance] SeparableRealBanach.normedAddCommGroup
  SeparableRealBanach.normedSpace SeparableRealBanach.completeSpace
  SeparableRealBanach.separableSpace

def ContainsLinearCopy (E : Type uE) (F : Type uF) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∃ (T : E →L[ℝ] F) (a : ℝ), 0 < a ∧ ∀ x : E, a * ‖x‖ ≤ ‖T x‖

def MainClaim : Prop :=
  ∃ X Y : SeparableRealBanach,
    ∃ Ψ : X.Carrier ≃ Y.Carrier,
      (∀ s t : X.Carrier,
        (4 / 21 : ℝ) * ‖s - t‖ ≤ ‖Ψ s - Ψ t‖ ∧
        ‖Ψ s - Ψ t‖ ≤ (76 / 25 : ℝ) * ‖s - t‖) ∧
      IsEmpty (X.Carrier ≃L[ℝ] Y.Carrier) ∧
      Nonempty (C0L2 →ₗᵢ[ℝ] X.Carrier) ∧
      ¬ ContainsLinearCopy C0L2 Y.Carrier

def main_statement : Prop :=
  MainClaim

end LipschitzCounterexample
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.LipschitzCounterexample.main_statement

end Problem

/- Formalization scope, from lean/docs/324.md: The formalized counterexample gives separable real Banach spaces $X,Y$ that are bi-Lipschitz equivalent but not linearly isomorphic. The bijection has lower Lipschitz bound $4/21$ and upper bound $76/25$. The linear obstruction is explicit: $X$ contains a linear isometric copy of $c_0(\ell_2)$, whereas $Y$ contains no bounded linear copy of that space. The formalized result constructs one separable real Banach space $X$ that is bi-Lipschitz equivalent to $X\times c_0$ but contains no closed linear subspace isomorphic to $c_0$. The same space contains a bi-Lipschitz copy of $c_0$, is bi-Lipschitz universal for separable metric spaces, and is not linearly isomorphic to $X\times c_0$. Thus nonlinear absorption of $c_0$ does not force a linear copy of it. -/
