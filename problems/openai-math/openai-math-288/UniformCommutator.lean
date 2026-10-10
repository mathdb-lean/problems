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

- problem_id: UniformCommutator
- collection: openai-math
- question_id: openai-math:288
- source: openai-math
- source_locator: lean/ComparatorChallenges/UniformCommutator.lean#OAI.Kadison.uniform_commutator
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Kadison's similarity conjecture: every bounded complex-linear unital algebra homomorphism from a unital complex C∗-algebra to operators on a Hilbert space becomes a $`*`$-homomorphism after conjugation by a bounded invertible operator. ([Lean](lean/docs/288.md)) We prove that every bounded complex-linear unital algebra homomorphism from a unital complex C∗-algebra into the bounded operators on an arbitrary Hilbert space is similar to a $`*`$-homomorphism. This resolves Kadison's similarity conjecture positively. We also obtain one universal hyperreflexivity constant for all unital von Neumann algebras on arbitrary complex Hilbert spaces.
- notes: OpenAI math result family 288, Kadison's similarity conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/288.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Kadison.uniform_commutator
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.Commutator.Main
- source_papers: preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf
- source_scope_note: lean/docs/288.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
universe u v
namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

def commutatorSeminorm (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) : ℝ :=
  sSup {r : ℝ | ∃ a : K →L[ℂ] K, a ∈ P ∧ ‖a‖ ≤ 1 ∧ r = ‖Y * a - a * Y‖}

def matrixOperator (h : ℕ) (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) :
    (PiLp 2 fun _ : Fin h => K) →L[ℂ] (PiLp 2 fun _ : Fin h => K) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin h => K)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ∑ j : Fin h,
      (X i j).comp (PiLp.proj 2 (fun _ : Fin h => K) j)))

def diagonalAmplification (h : ℕ) (Y : K →L[ℂ] K) :
    (PiLp 2 fun _ : Fin h => K) →L[ℂ] (PiLp 2 fun _ : Fin h => K) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin h => K)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => Y.comp (PiLp.proj 2 (fun _ : Fin h => K) i)))

def uniform_commutator_statement : Prop :=
  ∀ {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K)
      (h : ℕ), 1 ≤ h → ∀ (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)),
      (∀ i j, X i j ∈ P) →
      ‖diagonalAmplification h Y * matrixOperator h X -
        matrixOperator h X * diagonalAmplification h Y‖ ≤
        C * commutatorSeminorm P Y * ‖matrixOperator h X‖

end Kadison

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.Kadison.uniform_commutator_statement.{u}

end Problem

/- Formalization scope, from lean/docs/288.md: Kadison's similarity problem asks whether every bounded unital homomorphism from a unital complex $C^*$-algebra into operators on a Hilbert space is similar to a $*$-homomorphism. The formalization proves this for arbitrary Hilbert spaces. It also gives one universal hyperreflexivity constant for all unital von Neumann algebras. The linked commutator estimate is uniform over all finite matrix amplifications: its constant is independent of the algebra, Hilbert space, and amplification size. This is the quantitative derivation estimate supporting the similarity result. -/
