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

- problem_id: C0Absorption
- collection: openai-math
- question_id: openai-math:324
- source: openai-math
- source_locator: lean/ComparatorChallenges/C0Absorption.lean#OAI.C0Absorption.main_result
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs separable real Banach spaces that are globally bi-Lipschitz equivalent but not linearly isomorphic, resolving the separable Lipschitz-isomorphism problem negatively. Thus even the complete metric structure up to bi-Lipschitz equivalence does not determine a separable Banach space's linear isomorphism class. ([Lean](lean/docs/324.md)) There are separable real Banach spaces that are globally bi-Lipschitz equivalent but not linearly isomorphic. This gives a negative answer to the separable Banach-space Lipschitz-isomorphism problem. We construct a separable real Banach space Z that contains no linear copy of c0, yet is bi-Lipschitz equivalent to $`Z\oplus_\infty c_0`$. The same space contains a bi-Lipschitz image of every separable metric space.
- notes: OpenAI math result family 324, Lipschitz equivalent Banach spaces need not be linearly isomorphic -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/324.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.C0Absorption.main_result
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.C0Absorption.Main
- source_main_result: OAI.C0Absorption.main_result
- source_papers: preprints/Lipschitz-Equivalent-Separable-Banach-Spaces-Need-Not-Be-Linearly-Isomorphic-September-24-2026/paper.pdf preprints/Bi-Lipschitz-Absorption-of-c0-Without-a-Linear-Copy-of-c0-September-26-2026/paper.pdf
- source_scope_note: lean/docs/324.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace C0Absorption

open scoped ZeroAtInfty

abbrev C0 := C₀(ℕ, ℝ)

def BiLip {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ x y, c * dist x y ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ C * dist x y

def NoLinearC0 (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z] : Prop :=
  ∀ T : C0 →L[ℝ] Z, ¬ ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖T x‖

def MetricUniversal (Z : Type*) [MetricSpace Z] : Prop :=
  ∀ (M : Type) [MetricSpace M] [TopologicalSpace.SeparableSpace M],
    ∃ f : M → Z, BiLip f

def MainConclusion : Prop :=
  ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : NormedSpace ℝ Z),
    CompleteSpace Z ∧ TopologicalSpace.SeparableSpace Z ∧ NoLinearC0 Z ∧
    (∃ F : Z × C0 → Z, Function.Surjective F ∧ BiLip F) ∧
    (∃ f : C0 → Z, BiLip f) ∧ MetricUniversal Z ∧
    ¬ Nonempty ((Z × C0) ≃L[ℝ] Z)

def main_result_statement : Prop :=
  MainConclusion

end C0Absorption

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.C0Absorption.main_result_statement

end Problem

/- Formalization scope, from lean/docs/324.md: The formalized counterexample gives separable real Banach spaces $X,Y$ that are bi-Lipschitz equivalent but not linearly isomorphic. The bijection has lower Lipschitz bound $4/21$ and upper bound $76/25$. The linear obstruction is explicit: $X$ contains a linear isometric copy of $c_0(\ell_2)$, whereas $Y$ contains no bounded linear copy of that space. The formalized result constructs one separable real Banach space $X$ that is bi-Lipschitz equivalent to $X\times c_0$ but contains no closed linear subspace isomorphic to $c_0$. The same space contains a bi-Lipschitz copy of $c_0$, is bi-Lipschitz universal for separable metric spaces, and is not linearly isomorphic to $X\times c_0$. Thus nonlinear absorption of $c_0$ does not force a linear copy of it. -/
