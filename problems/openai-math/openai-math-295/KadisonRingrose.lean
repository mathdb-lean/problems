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

- problem_id: KadisonRingrose
- collection: openai-math
- question_id: openai-math:295
- source: openai-math
- source_locator: lean/ComparatorChallenges/KadisonRingrose.lean#OAI.BoundedHochschild.KadisonRingrose.main_result
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that every bounded Hochschild cocycle of degree at least two on a complex von Neumann algebra, with coefficients in the algebra itself, has a bounded primitive. Equivalently, all higher bounded Hochschild cohomology groups vanish, resolving the Kadison–Ringrose conjecture. ([Lean](lean/docs/295.md)) We prove that every bounded Hochschild cocycle of degree at least two on a complex von Neumann algebra, with values in the algebra itself, has a bounded primitive. Together with the established degree-one inner-derivation theorem, this resolves the Kadison–Ringrose cohomology conjecture positively.
- notes: OpenAI math result family 295, The Kadison–Ringrose cohomology conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/295.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.BoundedHochschild.KadisonRingrose.main_result
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.BoundedHochschild.MainResult
- source_papers: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf
- source_scope_note: lean/docs/295.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! Every ordinary bounded higher Hochschild cocycle of a complex von Neumann
algebra is the coboundary of a bounded cochain with values in the same algebra. -/

noncomputable section

namespace BoundedHochschild

abbrev Cochain (M : Type*) [NormedAddCommGroup M] [NormedSpace ℂ M] (n : ℕ) :=
  ContinuousMultilinearMap ℂ (fun _ : Fin n => M) M

def mergeInputs {M : Type*} [Mul M] {n : ℕ}
    (v : Fin (n + 1) → M) (j : Fin n) : Fin n → M :=
  fun i => if i < j then v i.castSucc
    else if i = j then v i.castSucc * v i.succ else v i.succ

noncomputable def differentialValue {M : Type*} [NormedRing M] [NormedAlgebra ℂ M]
    {n : ℕ} (f : Cochain M n) (v : Fin (n + 1) → M) : M :=
  v 0 * f (fun i => v i.succ) +
    ∑ j : Fin n, ((-1 : ℂ) ^ (j.val + 1)) • f (mergeInputs v j) +
    ((-1 : ℂ) ^ (n + 1)) • (f (fun i => v i.castSucc) * v (Fin.last n))

namespace KadisonRingrose

universe u

def main_result_statement : Prop :=
  ∀ {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M] (n : ℕ) (f : Cochain M (n + 2)) (hf : ∀ x : Fin (n + 3) → M, differentialValue f x = 0),
    ∃ g : Cochain M (n + 1), ∀ x : Fin (n + 2) → M,
      differentialValue g x = f x

end KadisonRingrose
end BoundedHochschild

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.BoundedHochschild.KadisonRingrose.main_result_statement.{u}

end Problem

/- Formalization scope, from lean/docs/295.md: The formalization proves vanishing of bounded Hochschild cohomology in every degree at least two for a complex von Neumann algebra with coefficients in itself. Every bounded multilinear cocycle of such a degree is the Hochschild differential of a bounded multilinear cochain one degree lower. No separability or type restriction is imposed. The degree-one inner-derivation theorem is outside this selected statement. -/
